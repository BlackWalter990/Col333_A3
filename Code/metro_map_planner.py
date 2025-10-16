#!/usr/bin/env python3
import sys
import os

class MetroMapPlanner:
    def __init__(self):
        self.scenario = 0
        self.N = 0
        self.M = 0
        self.K = 0
        self.J = 0
        self.P = 0
        self.starts = []
        self.ends = []
        self.popular = []
        self.var_counter = 0
        self.clauses = []
        self.var_map = {}
        
    def parse_input(self, filename):
        """Parse the input .city file"""
        with open(filename, 'r') as f:
            lines = f.readlines()
        
        lines = [line.strip() for line in lines if line.strip()]
        
        self.scenario = int(lines[0])
        params = list(map(int, lines[1].split()))
        
        if self.scenario == 1:
            self.N, self.M, self.K, self.J = params
            self.P = 0
        else:
            self.N, self.M, self.K, self.J, self.P = params
        
        for i in range(self.K):
            sx, sy, ex, ey = map(int, lines[2 + i].split())
            self.starts.append((sx, sy))
            self.ends.append((ex, ey))
        
        if self.scenario == 2:
            popular_coords = list(map(int, lines[2 + self.K].split()))
            for i in range(self.P):
                x = popular_coords[2 * i]
                y = popular_coords[2 * i + 1]
                self.popular.append((x, y))
    
    def get_var(self, *args):
        """Get or create a SAT variable"""
        var_name = "_".join(map(str, args))
        
        if var_name not in self.var_map:
            self.var_counter += 1
            self.var_map[var_name] = self.var_counter
        
        return self.var_map[var_name]
    
    def add_clause(self, literals):
        """Add a clause to the SAT formula"""
        if literals:
            self.clauses.append(literals)
    
    def encode_at_most_one(self, variables):
        """Encode at-most-one constraint using pairwise encoding"""
        for i in range(len(variables)):
            for j in range(i + 1, len(variables)):
                self.add_clause([-variables[i], -variables[j]])
    
    def encode_exactly_one(self, variables):
        """Encode exactly-one constraint"""
        if not variables:
            return
        self.add_clause(list(variables))
        self.encode_at_most_one(variables)
    
    def encode_cell_constraints(self):
        """Constraint 1: At most 1 metro line per cell"""
        for x in range(self.N):
            for y in range(self.M):
                cell_vars = []
                for k in range(self.K):
                    cell_vars.append(self.get_var("C", x, y, k))
                self.encode_at_most_one(cell_vars)
    
    def encode_path_constraints(self):
        """Constraint 2: Every metro line k is a path from s_k to e_k"""
        for k in range(self.K):
            sx, sy = self.starts[k]
            ex, ey = self.ends[k]
            
            # Start and end cells must be part of the path
            self.add_clause([self.get_var("C", sx, sy, k)])
            self.add_clause([self.get_var("C", ex, ey, k)])
            
            directions = {'L': (-1, 0), 'R': (1, 0), 'U': (0, -1), 'D': (0, 1)}
            
            for x in range(self.N):
                for y in range(self.M):
                    cell_var = self.get_var("C", x, y, k)
                    
                    # If not on path, no directions
                    for d in directions:
                        self.add_clause([-self.get_var("D", x, y, k, d), cell_var])
                    
                    # Start cell
                    if (x, y) == (sx, sy):
                        out_dirs = []
                        for d, (dx, dy) in directions.items():
                            nx, ny = x + dx, y + dy
                            if 0 <= nx < self.N and 0 <= ny < self.M:
                                out_dirs.append(self.get_var("D", x, y, k, d))
                        self.encode_exactly_one(out_dirs)
                        
                        # No incoming edges
                        for d, (dx, dy) in directions.items():
                            px, py = x - dx, y - dy
                            if 0 <= px < self.N and 0 <= py < self.M:
                                self.add_clause([-self.get_var("D", px, py, k, d)])
                    
                    # End cell
                    elif (x, y) == (ex, ey):
                        # No outgoing
                        for d in directions:
                            self.add_clause([-self.get_var("D", x, y, k, d)])
                        
                        # Exactly one incoming
                        inc_dirs = []
                        for d, (dx, dy) in directions.items():
                            px, py = x - dx, y - dy
                            if 0 <= px < self.N and 0 <= py < self.M:
                                inc_dirs.append(self.get_var("D", px, py, k, d))
                        self.encode_exactly_one(inc_dirs)
                    
                    # Intermediate cells
                    else:
                        out_dirs = []
                        for d, (dx, dy) in directions.items():
                            nx, ny = x + dx, y + dy
                            if 0 <= nx < self.N and 0 <= ny < self.M:
                                out_dirs.append(self.get_var("D", x, y, k, d))
                        
                        inc_dirs = []
                        for d, (dx, dy) in directions.items():
                            px, py = x - dx, y - dy
                            if 0 <= px < self.N and 0 <= py < self.M:
                                inc_dirs.append(self.get_var("D", px, py, k, d))
                        
                        # If on path, must have exactly one incoming and outgoing
                        if out_dirs:
                            self.add_clause([-cell_var] + out_dirs)
                            self.encode_at_most_one(out_dirs)
                        
                        if inc_dirs:
                            self.add_clause([-cell_var] + inc_dirs)
                            self.encode_at_most_one(inc_dirs)
                        
                        # If not on path, no directions
                        for v in out_dirs + inc_dirs:
                            self.add_clause([cell_var, -v])
                    
                    # Flow: if outgoing direction d, next cell must be on path
                    for d, (dx, dy) in directions.items():
                        nx, ny = x + dx, y + dy
                        if 0 <= nx < self.N and 0 <= ny < self.M:
                            dir_var = self.get_var("D", x, y, k, d)
                            next_cell = self.get_var("C", nx, ny, k)
                            self.add_clause([-dir_var, next_cell])
    
    def encode_turn_constraints(self):
        """Constraint 3: At most J turns in any metro line"""
        for k in range(self.K):
            sx, sy = self.starts[k]
            ex, ey = self.ends[k]
            
            # For each intermediate cell, define turn variable
            turn_vars = []
            
            for x in range(self.N):
                for y in range(self.M):
                    if (x, y) == (sx, sy) or (x, y) == (ex, ey):
                        continue
                    
                    turn_var = self.get_var("T", x, y, k)
                    turn_vars.append(turn_var)
                    
                    dirs = {'L': (-1, 0), 'R': (1, 0), 'U': (0, -1), 'D': (0, 1)}
                    
                    # Turn happens when incoming != outgoing direction
                    for d_in, (dx_in, dy_in) in dirs.items():
                        px, py = x - dx_in, y - dy_in
                        if not (0 <= px < self.N and 0 <= py < self.M):
                            continue
                        
                        in_var = self.get_var("D", px, py, k, d_in)
                        
                        for d_out, (dx_out, dy_out) in dirs.items():
                            nx, ny = x + dx_out, y + dy_out
                            if not (0 <= nx < self.N and 0 <= ny < self.M):
                                continue
                            
                            out_var = self.get_var("D", x, y, k, d_out)
                            
                            if d_in != d_out:
                                # Turn: in AND out => turn_var
                                self.add_clause([-in_var, -out_var, turn_var])
                            else:
                                # No turn: in AND out => NOT turn_var
                                self.add_clause([-in_var, -out_var, -turn_var])
            
            # At most J turns
            if self.J >= 0 and turn_vars:
                self.encode_at_most_k_simple(turn_vars, self.J)
    
    def encode_at_most_k_simple(self, variables, k):
        """Simple at-most-k encoding using binomial method"""
        n = len(variables)
        
        if k >= n:
            return  # Always satisfied
        
        if k < 0:
            for v in variables:
                self.add_clause([-v])
            return
        
        # For small k, use direct encoding: forbid all (k+1)-subsets
        # This works well when k is small (like 0, 1, 2, 3)
        if k <= 3:
            from itertools import combinations
            for subset in combinations(variables, k + 1):
                self.add_clause([-v for v in subset])
            return
        
        # For larger k, use sequential counter
        # s[i][j] = among first i variables, exactly j are true
        for i in range(n + 1):
            for j in range(min(i, k) + 2):
                s = self.get_var("SEQ", id(variables), i, j)
                
                if i == 0:
                    if j == 0:
                        self.add_clause([s])
                    else:
                        self.add_clause([-s])
                elif j > i:
                    self.add_clause([-s])
                else:
                    x = variables[i - 1]
                    
                    # s[i][j] = (x AND s[i-1][j-1]) OR (NOT x AND s[i-1][j])
                    if j == 0:
                        s_prev = self.get_var("SEQ", id(variables), i - 1, 0)
                        self.add_clause([-x, -s])
                        self.add_clause([x, -s_prev, s])
                        self.add_clause([-s, s_prev])
                    elif j <= k:
                        s_prev_j = self.get_var("SEQ", id(variables), i - 1, j)
                        s_prev_j1 = self.get_var("SEQ", id(variables), i - 1, j - 1)
                        
                        self.add_clause([-x, -s_prev_j1, s])
                        self.add_clause([x, -s_prev_j, s])
                        self.add_clause([-s, x, s_prev_j])
                        self.add_clause([-s, -x, s_prev_j1])
        
        # Enforce: at most k are true
        valid_states = []
        for j in range(k + 1):
            valid_states.append(self.get_var("SEQ", id(variables), n, j))
        self.add_clause(valid_states)
    
    def encode_popular_constraints(self):
        """Constraint 4: Every popular cell visited by at least one metro"""
        if self.scenario != 2:
            return
        
        for x, y in self.popular:
            popular_clause = []
            for k in range(self.K):
                popular_clause.append(self.get_var("C", x, y, k))
            self.add_clause(popular_clause)
    
    def encode_to_sat(self, output_file):
        """Encode the problem to SAT and write to output file"""
        self.var_counter = 0
        self.clauses = []
        self.var_map = {}
        
        self.encode_cell_constraints()
        self.encode_path_constraints()
        self.encode_turn_constraints()
        self.encode_popular_constraints()
        
        with open(output_file, 'w') as f:
            f.write(f"p cnf {self.var_counter} {len(self.clauses)}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
    
    def decode_sat_output(self, sat_output_file, output_file):
        """Decode the SAT output to metro map format"""
        if not os.path.exists(sat_output_file):
            with open(output_file, 'w') as f:
                f.write("0\n")
            return
        
        with open(sat_output_file, 'r') as f:
            lines = f.readlines()
        
        if not lines or lines[0].strip() == "UNSAT":
            with open(output_file, 'w') as f:
                f.write("0\n")
            return
        
        # Parse SAT assignments
        assignments = set()
        for line in lines[1:]:
            tokens = line.strip().split()
            for token in tokens:
                if token == '0':
                    break
                var_num = int(token)
                if var_num > 0:
                    assignments.add(var_num)
        
        # Reconstruct paths
        metro_paths = []
        for k in range(self.K):
            path = []
            x, y = self.starts[k]
            ex, ey = self.ends[k]
            
            while (x, y) != (ex, ey):
                found = False
                for d in ['L', 'R', 'U', 'D']:
                    dir_var = self.get_var("D", x, y, k, d)
                    if dir_var in assignments:
                        path.append(d)
                        if d == 'L':
                            x -= 1
                        elif d == 'R':
                            x += 1
                        elif d == 'U':
                            y -= 1
                        elif d == 'D':
                            y += 1
                        found = True
                        break
                
                if not found:
                    break
            
            metro_paths.append(path)
        
        # Write output
        with open(output_file, 'w') as f:
            for path in metro_paths:
                f.write(" ".join(path) + " 0\n")

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 metro_map_planner.py <basename>")
        sys.exit(1)
    
    basename = sys.argv[1]
    planner = MetroMapPlanner()
    planner.parse_input(f"{basename}.city")
    planner.encode_to_sat(f"{basename}.satinput")
    
    if os.path.exists(f"{basename}.satoutput"):
        planner.decode_sat_output(f"{basename}.satoutput", f"{basename}.metromap")

if __name__ == "__main__":
    main()