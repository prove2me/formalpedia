-- Prove2me | solution 1 for BSS.decisionInNP_of_decisionInP
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:23:02.091101+00:00
-- url     : https://prove2.me/submissions/3ddaf8e0-9c3d-4b09-94e8-4ded41dbde9b

import Definitions.Def_BSSFeasibility

namespace BSS
namespace PNP

open MvPolynomial

noncomputable section

/-! ### Generic facts about machines -/

lemma step_comp {M : Machine ℝ} {c : M.Config} {g : PolyMapInf ℝ} {iOp jOp : ShiftOp}
    {next : Fin M.numNodes} (h : M.nodes c.1 = Node.computation g iOp jOp next) :
    M.step c = (next, iOp.apply c.2.1, jOp.apply c.2.2.1, g.eval c.2.2.2) := by
  unfold Machine.step; rw [h]

lemma step_branch {M : Machine ℝ} {c : M.Config} {k : ℕ} {hp : MvPolynomial (Fin k) ℝ}
    {ng ps : Fin M.numNodes} (h : M.nodes c.1 = Node.branch k hp ng ps) :
    M.step c = (if branchValue hp c.2.2.2 < 0 then ng else ps, c.2) := by
  unfold Machine.step; rw [h]

lemma step_fifth {M : Machine ℝ} {c : M.Config} {next : Fin M.numNodes}
    (h : M.nodes c.1 = Node.fifth next) :
    M.step c = (next, c.2.1, c.2.2.1, c.2.2.2.update c.2.2.1 (c.2.2.2 c.2.1)) := by
  unfold Machine.step; rw [h]

lemma step_output {M : Machine ℝ} {c : M.Config} (h : M.nodes c.1 = Node.output) :
    M.step c = c := by
  unfold Machine.step; rw [h]

lemma step_comp' {M : Machine ℝ} {a : Fin M.numNodes} {i j : ℕ} {x : Rinf ℝ} {g : PolyMapInf ℝ}
    {iOp jOp : ShiftOp} {next : Fin M.numNodes} (h : M.nodes a = Node.computation g iOp jOp next) :
    M.step (a, i, j, x) = (next, iOp.apply i, jOp.apply j, g.eval x) := step_comp h

lemma step_branch' {M : Machine ℝ} {a : Fin M.numNodes} {i j : ℕ} {x : Rinf ℝ} {k : ℕ}
    {hp : MvPolynomial (Fin k) ℝ} {ng ps : Fin M.numNodes} (h : M.nodes a = Node.branch k hp ng ps) :
    M.step (a, i, j, x) = (if branchValue hp x < 0 then ng else ps, i, j, x) := step_branch h

lemma step_fifth' {M : Machine ℝ} {a : Fin M.numNodes} {i j : ℕ} {x : Rinf ℝ} {next : Fin M.numNodes}
    (h : M.nodes a = Node.fifth next) :
    M.step (a, i, j, x) = (next, i, j, x.update j (x i)) := step_fifth h

lemma isOutput_iff {N : ℕ} (nd : Node ℝ N) : nd.IsOutput ↔ nd = Node.output := by
  cases nd <;> simp [Node.IsOutput]

lemma iterate_output {M : Machine ℝ} {c : M.Config} (h : (M.nodes c.1).IsOutput) (s : ℕ) :
    M.step^[s] c = c := by
  rw [isOutput_iff] at h
  induction s with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply', ih, step_output h]

lemma run_add (M : Machine ℝ) (y : Rinf ℝ) (a b : ℕ) :
    M.run y (a + b) = M.step^[a] (M.run y b) := by
  unfold Machine.run; rw [Function.iterate_add_apply]

lemma halting_spec {M : Machine ℝ} {y : Rinf ℝ} {T : ℕ} (h : M.HaltsBy y T) :
    M.haltingTime y ≤ T ∧ M.output y = (M.run y T).2.2.2 := by
  have hne : ({T : ℕ | M.HaltsBy y T} : Set ℕ).Nonempty := ⟨T, h⟩
  have h0 : M.HaltsBy y (M.haltingTime y) := Nat.sInf_mem hne
  have hle : M.haltingTime y ≤ T := Nat.sInf_le h
  refine ⟨hle, ?_⟩
  unfold Machine.output
  have : T = (T - M.haltingTime y) + M.haltingTime y := by omega
  rw [this, run_add, iterate_output h0]

/-! ### Polynomial maps -/

def XV {d : ℕ} (i : ℕ) : MvPolynomial (Fin d) ℝ := if h : i < d then X ⟨i, h⟩ else 0

def pm (d : ℕ) (F : ℕ → MvPolynomial (Fin d) ℝ) : PolyMapInf ℝ := ⟨d, fun c => F c.val⟩

lemma eval_XV {d : ℕ} (x : Rinf ℝ) (i : ℕ) (h : i < d) :
    MvPolynomial.eval (fun j : Fin d => x (j : ℕ)) (XV i) = x i := by
  simp [XV, h]

lemma polyEval_apply (g : PolyMapInf ℝ) (x : Rinf ℝ) (i : ℕ) :
    g.eval x i = if h : i < g.dim then
      MvPolynomial.eval (fun j : Fin g.dim => x (j : ℕ)) (g.coord ⟨i, h⟩) else x i := by
  unfold PolyMapInf.eval; rw [Finsupp.onFinset_apply]

lemma pm_apply (d : ℕ) (F : ℕ → MvPolynomial (Fin d) ℝ) (x : Rinf ℝ) (i : ℕ) :
    (pm d F).eval x i =
      if i < d then MvPolynomial.eval (fun j : Fin d => x (j : ℕ)) (F i) else x i := by
  rw [polyEval_apply]; simp only [pm]; by_cases h : i < d <;> simp [h] <;> rfl

def idMap : PolyMapInf ℝ := pm 0 (fun _ => 0)

lemma idMap_eval (x : Rinf ℝ) : idMap.eval x = x := by
  ext i; rw [idMap, pm_apply]; simp

/-- Stride-two copy of a polynomial map: coordinate `m` of the original lives at `2m`. -/
def g2 (g : PolyMapInf ℝ) : PolyMapInf ℝ :=
  pm (2 * g.dim) (fun c => if h : c % 2 = 0 ∧ c / 2 < g.dim then
    rename (fun v : Fin g.dim => (⟨2 * v.val, by omega⟩ : Fin (2 * g.dim))) (g.coord ⟨c / 2, h.2⟩)
    else XV c)

def h2 {k : ℕ} (hp : MvPolynomial (Fin k) ℝ) : MvPolynomial (Fin (2 * k)) ℝ :=
  rename (fun v : Fin k => (⟨2 * v.val, by omega⟩ : Fin (2 * k))) hp

lemma g2_even (g : PolyMapInf ℝ) (x x' : Rinf ℝ) (hx : ∀ m, x' (2 * m) = x m) (m : ℕ) :
    (g2 g).eval x' (2 * m) = g.eval x m := by
  rw [g2, pm_apply, polyEval_apply]
  by_cases hm : m < g.dim
  · have h1 : 2 * m < 2 * g.dim := by omega
    have h2' : (2 * m) % 2 = 0 ∧ 2 * m / 2 < g.dim := by omega
    rw [if_pos h1, dif_pos h2', dif_pos hm, eval_rename]
    have : (2 * m) / 2 = m := by omega
    have hf : ((fun j : Fin (2 * g.dim) => x' (j : ℕ)) ∘
        fun v : Fin g.dim => (⟨2 * v.val, by omega⟩ : Fin (2 * g.dim))) = fun j : Fin g.dim => x (j : ℕ) := by
      funext v; simp [Function.comp, hx]
    rw [hf]
    simp only [this]
  · have h1 : ¬ 2 * m < 2 * g.dim := by omega
    rw [if_neg h1, dif_neg hm, hx]

lemma h2_value {k : ℕ} (hp : MvPolynomial (Fin k) ℝ) (x x' : Rinf ℝ) (hx : ∀ m, x' (2 * m) = x m) :
    branchValue (h2 hp) x' = branchValue hp x := by
  unfold branchValue h2
  rw [eval_rename]
  have hf : ((fun j : Fin (2 * k) => x' (j : ℕ)) ∘
      fun v : Fin k => (⟨2 * v.val, by omega⟩ : Fin (2 * k))) = fun j : Fin k => x (j : ℕ) := by
    funext v; simp [Function.comp, hx]
  rw [hf]

/-! ### The machine -/

variable (M : Machine ℝ)

abbrev NN : ℕ := 16 + 2 * M.numNodes

def fi (v : ℕ) : Fin (NN M) := ⟨v % NN M, Nat.mod_lt _ (by unfold NN; omega)⟩

lemma fi_val {v : ℕ} (h : v < NN M) : (fi M v).val = v := Nat.mod_eq_of_lt h

def simIdx (n : Fin M.numNodes) : Fin (NN M) := fi M (16 + 2 * n.val)

def P0map : PolyMapInf ℝ := pm 7 fun
  | 2 => XV 0
  | 4 => 1
  | 6 => 0
  | c => XV c

def B3a : PolyMapInf ℝ := pm 7 fun
  | 2 => XV 2 - 2
  | 4 => XV 6 + 1
  | 6 => XV 6 + 1
  | c => XV c

def B3b : PolyMapInf ℝ := pm 7 fun
  | 2 => XV 2 - 2
  | 6 => XV 6 + 1
  | c => XV c

def A0map : PolyMapInf ℝ := pm 7 fun
  | 0 => XV 4
  | 1 => XV 2 + 2 * XV 6 - 2
  | 2 => XV 1
  | 4 => 0
  | 6 => 0
  | c => XV c

def A3map : PolyMapInf ℝ := pm 2 fun
  | 1 => XV 1 - 2
  | c => XV c

def preNode : ℕ → Node ℝ (NN M)
  | 0 => .computation P0map .inc .reset (fi M 1)
  | 1 => .branch 3 (-XV 2) (fi M 2) (fi M 7)
  | 2 => .fifth (fi M 3)
  | 3 => .branch 1 (-(XV 0) ^ 2) (fi M 4) (fi M 5)
  | 4 => .computation B3a .inc .inc (fi M 6)
  | 5 => .computation B3b .inc .inc (fi M 6)
  | 6 => .computation idMap .inc .reset (fi M 1)
  | 7 => .computation A0map .reset .inc (fi M 8)
  | 8 => .computation idMap .inc .inc (fi M 9)
  | 9 => .computation idMap .inc .inc (fi M 10)
  | 10 => .computation idMap .inc .inc (fi M 11)
  | 11 => .branch 2 (-XV 1) (fi M 12) (fi M 15)
  | 12 => .fifth (fi M 13)
  | 13 => .computation A3map .inc .inc (fi M 14)
  | 14 => .computation idMap .inc .inc (fi M 11)
  | _ => .computation idMap .reset .reset (simIdx M M.entry)

def firstNode (n : Fin M.numNodes) : Node ℝ (NN M) :=
  match M.nodes n with
  | .output => .output
  | .computation g iOp jOp _ => .computation (g2 g) iOp jOp (fi M (16 + 2 * n.val + 1))
  | .branch k hp ng ps => .branch (2 * k) (h2 hp) (simIdx M ng) (simIdx M ps)
  | .fifth next => .fifth (simIdx M next)

def secondNode (n : Fin M.numNodes) : Node ℝ (NN M) :=
  match M.nodes n with
  | .computation _ iOp jOp next => .computation idMap iOp jOp (simIdx M next)
  | _ => .output

def nodes' (i : Fin (NN M)) : Node ℝ (NN M) :=
  if h0 : i.val < 16 then preNode M i.val
  else if (i.val - 16) % 2 = 0 then firstNode M ⟨(i.val - 16) / 2, by have := i.2; unfold NN at this; omega⟩
  else secondNode M ⟨(i.val - 16) / 2, by have := i.2; unfold NN at this; omega⟩

abbrev sim : Machine ℝ := ⟨NN M, nodes' M, fi M 0⟩

lemma sim_pre {v : ℕ} (hv : v < 16) : (sim M).nodes (fi M v) = preNode M v := by
  show nodes' M (fi M v) = _
  have h1 : (fi M v).val = v := fi_val M (by unfold NN; omega)
  unfold nodes'; rw [dif_pos (by omega)]; simp only [h1]

lemma sim_first (n : Fin M.numNodes) : (sim M).nodes (simIdx M n) = firstNode M n := by
  show nodes' M (simIdx M n) = _
  have h1 : (simIdx M n).val = 16 + 2 * n.val := fi_val M (by have := n.2; unfold NN; omega)
  unfold nodes'
  rw [dif_neg (by omega), if_pos (by omega)]
  congr 1; ext; simp only [h1]; omega

lemma sim_second (n : Fin M.numNodes) :
    (sim M).nodes (fi M (16 + 2 * n.val + 1)) = secondNode M n := by
  show nodes' M _ = _
  have h1 : (fi M (16 + 2 * n.val + 1)).val = 16 + 2 * n.val + 1 := fi_val M (by have := n.2; unfold NN; omega)
  unfold nodes'
  rw [dif_neg (by omega), if_neg (by omega)]
  congr 1; ext; simp only [h1]; omega

/-! ### Simulation of `M` -/

def Rel (c : M.Config) (c' : (sim M).Config) : Prop :=
  c'.1 = simIdx M c.1 ∧ c'.2.1 = 2 * c.2.1 ∧ c'.2.2.1 = 2 * c.2.2.1 ∧
    ∀ m, c'.2.2.2 (2 * m) = c.2.2.2 m

lemma shift2 (op : ShiftOp) (r : ℕ) : op.apply (op.apply (2 * r)) = 2 * op.apply r := by
  cases op <;> simp [ShiftOp.apply] <;> omega

lemma sim_step (c : M.Config) (c' : (sim M).Config) (h : Rel M c c') :
    ∃ s ≤ 2, Rel M (M.step c) ((sim M).step^[s] c') := by
  obtain ⟨n, i, j, x⟩ := c
  obtain ⟨n', i', j', x'⟩ := c'
  obtain ⟨h1, h2', h3, h4⟩ := h
  simp only at h1 h2' h3 h4
  subst h1 h2' h3
  cases hn : M.nodes n with
  | output =>
    refine ⟨0, by omega, ?_⟩
    rw [step_output hn]; exact ⟨rfl, rfl, rfl, h4⟩
  | computation g iOp jOp next =>
    refine ⟨2, le_rfl, ?_⟩
    rw [step_comp hn]
    have e1 : (sim M).nodes (simIdx M n) = .computation (g2 g) iOp jOp (fi M (16 + 2 * n.val + 1)) := by
      rw [sim_first]; unfold firstNode; rw [hn]
    have e2 : (sim M).nodes (fi M (16 + 2 * n.val + 1)) = .computation idMap iOp jOp (simIdx M next) := by
      rw [sim_second]; unfold secondNode; rw [hn]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [step_comp' e1]
    rw [step_comp' e2]
    refine ⟨rfl, shift2 _ _, shift2 _ _, ?_⟩
    intro m; simp only; rw [idMap_eval]; exact g2_even g x x' h4 m
  | branch k hp ng ps =>
    refine ⟨1, by omega, ?_⟩
    rw [step_branch hn]
    have e1 : (sim M).nodes (simIdx M n) = .branch (2 * k) (h2 hp) (simIdx M ng) (simIdx M ps) := by
      rw [sim_first]; unfold firstNode; rw [hn]
    simp only [Function.iterate_one]
    rw [step_branch' e1]
    simp only [h2_value hp x x' h4]
    refine ⟨?_, rfl, rfl, h4⟩
    split_ifs <;> rfl
  | fifth next =>
    refine ⟨1, by omega, ?_⟩
    rw [step_fifth hn]
    have e1 : (sim M).nodes (simIdx M n) = .fifth (simIdx M next) := by
      rw [sim_first]; unfold firstNode; rw [hn]
    simp only [Function.iterate_one]
    rw [step_fifth' e1]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro m
    simp only [Finsupp.update_apply, h4]
    by_cases hm : m = j
    · subst hm; simp
    · rw [if_neg (by omega), if_neg hm]

lemma sim_run (c : M.Config) (c' : (sim M).Config) (h : Rel M c c') (t : ℕ) :
    ∃ s ≤ 2 * t, Rel M (M.step^[t] c) ((sim M).step^[s] c') := by
  induction t with
  | zero => exact ⟨0, le_rfl, h⟩
  | succ t ih =>
    obtain ⟨s, hs, hr⟩ := ih
    obtain ⟨s2, hs2, hr2⟩ := sim_step M _ _ hr
    refine ⟨s2 + s, by omega, ?_⟩
    rw [Function.iterate_succ_apply', Function.iterate_add_apply]
    exact hr2

lemma rel_output {c : M.Config} {c' : (sim M).Config} (h : Rel M c c')
    (ho : (M.nodes c.1).IsOutput) : ((sim M).nodes c'.1).IsOutput := by
  rw [isOutput_iff] at ho ⊢
  rw [h.1, sim_first]; unfold firstNode; rw [ho]

/-! ### Node behaviour of the preprocessing -/

section nodes
variable {M}
variable (i j : ℕ) (X : Rinf ℝ)

lemma bv_negX {d : ℕ} (v : ℕ) (hv : v < d) :
    branchValue (-XV v : MvPolynomial (Fin d) ℝ) X = - X v := by
  unfold branchValue; simp [eval_XV _ _ hv]

lemma bv_negsq : branchValue (-(XV 0) ^ 2 : MvPolynomial (Fin 1) ℝ) X = - (X 0) ^ 2 := by
  unfold branchValue; simp [XV]

lemma nd0 : (sim M).step (fi M 0, i, j, X) = (fi M 1, i + 1, 0, P0map.eval X) :=
  step_comp' (M := sim M) (a := fi M 0) (by rw [sim_pre M (v := 0) (by norm_num)]; rfl)
lemma nd1 : (sim M).step (fi M 1, i, j, X) = (if -(X 2) < 0 then fi M 2 else fi M 7, i, j, X) := by
  rw [step_branch' (M := sim M) (a := fi M 1) (by rw [sim_pre M (v := 1) (by norm_num)]; rfl), bv_negX X 2 (by norm_num)]
lemma nd2 : (sim M).step (fi M 2, i, j, X) = (fi M 3, i, j, X.update j (X i)) :=
  step_fifth' (M := sim M) (a := fi M 2) (by rw [sim_pre M (v := 2) (by norm_num)]; rfl)
lemma nd3 : (sim M).step (fi M 3, i, j, X) = (if -(X 0) ^ 2 < 0 then fi M 4 else fi M 5, i, j, X) := by
  rw [step_branch' (M := sim M) (a := fi M 3) (by rw [sim_pre M (v := 3) (by norm_num)]; rfl), bv_negsq X]
lemma nd4 : (sim M).step (fi M 4, i, j, X) = (fi M 6, i + 1, j + 1, B3a.eval X) :=
  step_comp' (M := sim M) (a := fi M 4) (by rw [sim_pre M (v := 4) (by norm_num)]; rfl)
lemma nd5 : (sim M).step (fi M 5, i, j, X) = (fi M 6, i + 1, j + 1, B3b.eval X) :=
  step_comp' (M := sim M) (a := fi M 5) (by rw [sim_pre M (v := 5) (by norm_num)]; rfl)
lemma nd6 : (sim M).step (fi M 6, i, j, X) = (fi M 1, i + 1, 0, X) := by
  rw [step_comp' (M := sim M) (a := fi M 6) (by rw [sim_pre M (v := 6) (by norm_num)]; rfl), idMap_eval]; rfl
lemma nd7 : (sim M).step (fi M 7, i, j, X) = (fi M 8, 0, j + 1, A0map.eval X) :=
  step_comp' (M := sim M) (a := fi M 7) (by rw [sim_pre M (v := 7) (by norm_num)]; rfl)
lemma nd8 : (sim M).step (fi M 8, i, j, X) = (fi M 9, i + 1, j + 1, X) := by
  rw [step_comp' (M := sim M) (a := fi M 8) (by rw [sim_pre M (v := 8) (by norm_num)]; rfl), idMap_eval]; rfl
lemma nd9 : (sim M).step (fi M 9, i, j, X) = (fi M 10, i + 1, j + 1, X) := by
  rw [step_comp' (M := sim M) (a := fi M 9) (by rw [sim_pre M (v := 9) (by norm_num)]; rfl), idMap_eval]; rfl
lemma nd10 : (sim M).step (fi M 10, i, j, X) = (fi M 11, i + 1, j + 1, X) := by
  rw [step_comp' (M := sim M) (a := fi M 10) (by rw [sim_pre M (v := 10) (by norm_num)]; rfl), idMap_eval]; rfl
lemma nd11 : (sim M).step (fi M 11, i, j, X) = (if -(X 1) < 0 then fi M 12 else fi M 15, i, j, X) := by
  rw [step_branch' (M := sim M) (a := fi M 11) (by rw [sim_pre M (v := 11) (by norm_num)]; rfl), bv_negX X 1 (by norm_num)]
lemma nd12 : (sim M).step (fi M 12, i, j, X) = (fi M 13, i, j, X.update j (X i)) :=
  step_fifth' (M := sim M) (a := fi M 12) (by rw [sim_pre M (v := 12) (by norm_num)]; rfl)
lemma nd13 : (sim M).step (fi M 13, i, j, X) = (fi M 14, i + 1, j + 1, A3map.eval X) :=
  step_comp' (M := sim M) (a := fi M 13) (by rw [sim_pre M (v := 13) (by norm_num)]; rfl)
lemma nd14 : (sim M).step (fi M 14, i, j, X) = (fi M 11, i + 1, j + 1, X) := by
  rw [step_comp' (M := sim M) (a := fi M 14) (by rw [sim_pre M (v := 14) (by norm_num)]; rfl), idMap_eval]; rfl
lemma nd15 : (sim M).step (fi M 15, i, j, X) = (simIdx M M.entry, 0, 0, X) := by
  rw [step_comp' (M := sim M) (a := fi M 15) (by rw [sim_pre M (v := 15) (by norm_num)]; rfl), idMap_eval]; rfl

end nodes

lemma P0_apply (X : Rinf ℝ) (i : ℕ) : P0map.eval X i =
    if i = 2 then X 0 else if i = 4 then 1 else if i = 6 then 0 else X i := by
  rw [P0map, pm_apply]
  by_cases hi : i < 7
  · rw [if_pos hi]; interval_cases i <;> simp [eval_XV]
  · rw [if_neg hi, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma B3a_apply (X : Rinf ℝ) (i : ℕ) : B3a.eval X i =
    if i = 2 then X 2 - 2 else if i = 4 then X 6 + 1 else if i = 6 then X 6 + 1 else X i := by
  rw [B3a, pm_apply]
  by_cases hi : i < 7
  · rw [if_pos hi]; interval_cases i <;> simp [eval_XV]
  · rw [if_neg hi, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma B3b_apply (X : Rinf ℝ) (i : ℕ) : B3b.eval X i =
    if i = 2 then X 2 - 2 else if i = 6 then X 6 + 1 else X i := by
  rw [B3b, pm_apply]
  by_cases hi : i < 7
  · rw [if_pos hi]; interval_cases i <;> simp [eval_XV]
  · rw [if_neg hi, if_neg (by omega), if_neg (by omega)]

lemma A0_apply (X : Rinf ℝ) (i : ℕ) : A0map.eval X i =
    if i = 0 then X 4 else if i = 1 then X 2 + 2 * X 6 - 2 else if i = 2 then X 1
    else if i = 4 then 0 else if i = 6 then 0 else X i := by
  rw [A0map, pm_apply]
  by_cases hi : i < 7
  · rw [if_pos hi]; interval_cases i <;> simp [eval_XV]
  · rw [if_neg hi, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

lemma A3_apply (X : Rinf ℝ) (i : ℕ) : A3map.eval X i = if i = 1 then X 1 - 2 else X i := by
  rw [A3map, pm_apply]
  by_cases hi : i < 2
  · rw [if_pos hi]; interval_cases i <;> simp [eval_XV]
  · rw [if_neg hi, if_neg (by omega)]

/-! ### Facts on inputs -/

lemma consInf_apply (v : ℝ) (q : Rinf ℝ) (i : ℕ) :
    consInf v q i = if i = 0 then v else q (i - 1) := by
  unfold consInf; rw [Finsupp.onFinset_apply]

lemma pair_apply (y y' : Rinf ℝ) (i : ℕ) :
    pairInf y y' i = if i % 2 = 0 then y (i / 2) else y' (i / 2) := by
  unfold pairInf; rw [Finsupp.onFinset_apply]

lemma pair_even (y y' : Rinf ℝ) (k : ℕ) : pairInf y y' (2 * k) = y k := by
  rw [pair_apply, if_pos (by omega)]; congr 1; omega

lemma pair_odd (y y' : Rinf ℝ) (k : ℕ) : pairInf y y' (2 * k + 1) = y' k := by
  rw [pair_apply, if_neg (by omega)]; congr 1; omega

lemma lt_lengthInf {x : Rinf ℝ} {i : ℕ} (h : x i ≠ 0) : i < lengthInf x := by
  have hmem : i ∈ x.support := Finsupp.mem_support_iff.mpr h
  have hs : x.support.Nonempty := ⟨i, hmem⟩
  unfold lengthInf; rw [dif_pos hs]
  have := Finset.le_max' _ i hmem; omega

lemma lengthInf_le {x : Rinf ℝ} {B : ℕ} (hB : 1 ≤ B) (h : ∀ i, x i ≠ 0 → i < B) :
    lengthInf x ≤ B := by
  unfold lengthInf; split_ifs with hs
  · have := h _ (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)); omega
  · exact hB

lemma one_le_lengthInf (x : Rinf ℝ) : 1 ≤ lengthInf x := by
  unfold lengthInf; split_ifs <;> omega

lemma zero_of_ge {x : Rinf ℝ} {i : ℕ} (h : lengthInf x ≤ i) : x i = 0 := by
  by_contra hc; have := lt_lengthInf hc; omega

def res (y : Rinf ℝ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => if y m ≠ 0 then m + 1 else res y m

lemma res_eq (y : Rinf ℝ) (m : ℕ) (h : ∀ k, m ≤ k → y k = 0) : res y m = lengthInf y := by
  induction m with
  | zero =>
    have : y = 0 := by ext k; exact h k (Nat.zero_le _)
    subst this; simp [res, lengthInf]
  | succ m ih =>
    by_cases hm : y m = 0
    · simp only [res, hm, ne_eq, not_true_eq_false, if_false]
      exact ih (fun k hk => by
        rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact hm
        · exact h k hk)
    · simp only [res, hm, ne_eq, not_false_eq_true, if_true]
      apply le_antisymm
      · exact Nat.succ_le_of_lt (lt_lengthInf hm)
      · apply lengthInf_le (by omega); intro i hi; by_contra hc; exact hi (h i (by omega))

lemma iter5 {α : Type} (f : α → α) (x : α) : f^[5] x = f (f (f (f (f x)))) := rfl
lemma iter4 {α : Type} (f : α → α) (x : α) : f^[4] x = f (f (f (f x))) := rfl
lemma iter2 {α : Type} (f : α → α) (x : α) : f^[2] x = f (f x) := rfl

/-! ### The preprocessing loops -/

section pre
variable (y y' : Rinf ℝ)

def InvB (L m : ℕ) (c : (sim M).Config) : Prop :=
  c.1 = fi M 1 ∧ c.2.1 = 2 * m + 1 ∧ c.2.2.1 = 0 ∧ c.2.2.2 2 = (L : ℝ) - 2 * m ∧
  c.2.2.2 6 = m ∧ c.2.2.2 4 = res y m ∧ (∀ k, c.2.2.2 (2 * k + 1) = y k) ∧
  (∀ k, 4 ≤ k → c.2.2.2 (2 * k) = y' (k - 1))

def InvA (L m : ℕ) (c : (sim M).Config) : Prop :=
  c.1 = fi M 11 ∧ c.2.1 = 2 * m + 1 ∧ c.2.2.1 = 2 * m + 2 ∧ c.2.2.2 0 = lengthInf y ∧
  c.2.2.2 1 = (L : ℝ) - 2 * m ∧ (∀ k, k < m → c.2.2.2 (2 * k + 2) = y k) ∧
  (∀ k, m ≤ k → c.2.2.2 (2 * k + 1) = y k) ∧
  (∀ k, m ≤ k → c.2.2.2 (2 * k + 2) = if k ≤ 2 then 0 else y' k)

lemma B_init (L : ℕ) :
    InvB M y y' L 0 ((sim M).step (fi M 0, 0, 0, consInf (L : ℝ) (pairInf y y'))) := by
  rw [nd0]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P0_apply]; simp [consInf_apply]
  · rw [P0_apply]; simp
  · rw [P0_apply]; simp [res]
  · intro k
    rw [P0_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), consInf_apply,
      if_neg (by omega), show 2 * k + 1 - 1 = 2 * k by omega, pair_even]
  · intro k hk
    rw [P0_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), consInf_apply,
      if_neg (by omega), show 2 * k - 1 = 2 * (k - 1) + 1 by omega, pair_odd]

lemma B_iter (L m : ℕ) (c : (sim M).Config) (h : InvB M y y' L m c) (hm : 2 * m < L) :
    InvB M y y' L (m + 1) ((sim M).step^[5] c) := by
  obtain ⟨a, i, j, X⟩ := c
  obtain ⟨h1, h2, h3, h4, h6, h4', hodd, hev⟩ := h
  simp only at h1 h2 h3 h4 h6 h4' hodd hev
  subst h1 h2 h3
  have hc : -(X 2) < 0 := by
    rw [h4]; have : ((2 * m : ℕ) : ℝ) < L := by exact_mod_cast hm
    push_cast at this; linarith
  rw [iter5, nd1, if_pos hc, nd2, nd3]
  have hu0 : (X.update 0 (X (2 * m + 1))) 0 = y m := by simp [Finsupp.update_apply, hodd]
  have hu : ∀ t, t ≠ 0 → (X.update 0 (X (2 * m + 1))) t = X t := by
    intro t ht; simp [Finsupp.update_apply, ht]
  by_cases hy : y m = 0
  · have hn : ¬ (-(X.update 0 (X (2 * m + 1)) 0) ^ 2 < 0) := by rw [hu0, hy]; simp
    rw [if_neg hn, nd5, nd6]
    refine ⟨rfl, by ring, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [B3b_apply, if_pos rfl, hu 2 (by norm_num), h4]; push_cast; ring
    · rw [B3b_apply, if_neg (by norm_num), if_pos rfl, hu 6 (by norm_num), h6]; push_cast; ring
    · rw [B3b_apply, if_neg (by norm_num), if_neg (by norm_num), hu 4 (by norm_num), h4']
      simp [res, hy]
    · intro k; rw [B3b_apply, if_neg (by omega), if_neg (by omega), hu _ (by omega), hodd]
    · intro k hk; rw [B3b_apply, if_neg (by omega), if_neg (by omega), hu _ (by omega), hev k hk]
  · have hp : (-(X.update 0 (X (2 * m + 1)) 0) ^ 2 < 0) := by
      rw [hu0]; have : 0 < (y m) ^ 2 := by positivity
      linarith
    rw [if_pos hp, nd4, nd6]
    refine ⟨rfl, by ring, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [B3a_apply, if_pos rfl, hu 2 (by norm_num), h4]; push_cast; ring
    · rw [B3a_apply, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, hu 6 (by norm_num), h6]
      push_cast; ring
    · rw [B3a_apply, if_neg (by norm_num), if_pos rfl, hu 6 (by norm_num), h6]
      simp [res, hy]
    · intro k
      rw [B3a_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), hu _ (by omega), hodd]
    · intro k hk
      rw [B3a_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), hu _ (by omega),
        hev k hk]

lemma A_init (L m : ℕ) (hL : L = lengthInf (pairInf y y')) (c : (sim M).Config)
    (h : InvB M y y' L m c) (hm : L ≤ 2 * m) :
    InvA M y y' L 1 ((sim M).step^[5] c) := by
  obtain ⟨a, i, j, X⟩ := c
  obtain ⟨h1, h2, h3, h4, h6, h4', hodd, hev⟩ := h
  simp only at h1 h2 h3 h4 h6 h4' hodd hev
  subst h1 h2 h3
  have hc : ¬ -(X 2) < 0 := by
    rw [h4]; have : (L : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this; linarith
  rw [iter5, nd1, if_neg hc, nd7, nd8, nd9, nd10]
  have hres : res y m = lengthInf y := by
    apply res_eq; intro k hk; by_contra hy
    have := lt_lengthInf (x := pairInf y y') (i := 2 * k) (by rw [pair_even]; exact hy)
    omega
  refine ⟨rfl, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A0_apply, if_pos rfl, h4', hres]
  · rw [A0_apply, if_neg (by norm_num), if_pos rfl, h4, h6]; push_cast; ring
  · intro k hk
    obtain rfl : k = 0 := by omega
    rw [A0_apply, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    simpa using hodd 0
  · intro k hk
    rw [A0_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), hodd]
  · intro k hk
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
    · norm_num [A0_apply]
    · norm_num [A0_apply]
    · rw [A0_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (show ¬ k ≤ 2 by omega), show 2 * k + 2 = 2 * (k + 1) by ring,
        hev (k + 1) (by omega)]
      simp

lemma A_iter (L m : ℕ) (c : (sim M).Config) (h : InvA M y y' L m c) (hm1 : 1 ≤ m)
    (hm : 2 * m < L) : InvA M y y' L (m + 1) ((sim M).step^[4] c) := by
  obtain ⟨a, i, j, X⟩ := c
  obtain ⟨h1, h2, h3, h0, hc1, hlow, hodd, hev⟩ := h
  simp only at h1 h2 h3 h0 hc1 hlow hodd hev
  subst h1 h2 h3
  have hc : -(X 1) < 0 := by
    rw [hc1]; have : ((2 * m : ℕ) : ℝ) < L := by exact_mod_cast hm
    push_cast at this; linarith
  rw [iter4, nd11, if_pos hc, nd12, nd13, nd14]
  have hu : ∀ t, (X.update (2 * m + 2) (X (2 * m + 1))) t =
      if t = 2 * m + 2 then y m else X t := by
    intro t; rw [Finsupp.update_apply, hodd m le_rfl]
  refine ⟨rfl, by ring, by ring, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A3_apply, if_neg (by norm_num), hu, if_neg (by omega), h0]
  · rw [A3_apply, if_pos rfl, hu, if_neg (by omega), hc1]; push_cast; ring
  · intro k hk
    rw [A3_apply, if_neg (by omega), hu]
    by_cases hkm : k = m
    · subst hkm; rw [if_pos rfl]
    · rw [if_neg (by omega), hlow k (by omega)]
  · intro k hk
    rw [A3_apply, if_neg (by omega), hu, if_neg (by omega), hodd k (by omega)]
  · intro k hk
    rw [A3_apply, if_neg (by omega), hu, if_neg (by omega), hev k (by omega)]

lemma A_exit (L m : ℕ) (c : (sim M).Config) (h : InvA M y y' L m c) (hm : L ≤ 2 * m) :
    (sim M).step^[2] c = (simIdx M M.entry, 0, 0, c.2.2.2) := by
  obtain ⟨a, i, j, X⟩ := c
  obtain ⟨h1, h2, h3, h0, hc1, hlow, hodd, hev⟩ := h
  simp only at h1 h2 h3 hc1
  subst h1 h2 h3
  have hc : ¬ -(X 1) < 0 := by
    rw [hc1]; have : (L : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this; linarith
  rw [iter2, nd11, if_neg hc, nd15]

lemma pre_spec : ∃ T ≤ 5 * lengthInf (pairInf y y') + 10, ∃ X : Rinf ℝ,
    (sim M).run (pairInf y y') T = (simIdx M M.entry, 0, 0, X) ∧
    ∀ k, X (2 * k) = consInf ((lengthInf y : ℕ) : ℝ) y k := by
  set L := lengthInf (pairInf y y') with hLdef
  have hL1 : 1 ≤ L := one_le_lengthInf _
  set ms := (L + 1) / 2 with hms
  have hms1 : 1 ≤ ms := by omega
  -- loop B
  have hB : ∀ m, m ≤ ms → InvB M y y' L m ((sim M).run (pairInf y y') (1 + 5 * m)) := by
    intro m
    induction m with
    | zero => intro _; exact B_init M y y' L
    | succ m ih =>
      intro hm
      rw [show 1 + 5 * (m + 1) = 5 + (1 + 5 * m) by ring, run_add]
      exact B_iter M y y' L m _ (ih (by omega)) (by omega)
  have hA1 := A_init M y y' L ms hLdef _ (hB ms le_rfl) (by omega)
  rw [← run_add] at hA1
  have hA : ∀ d, 1 + d ≤ ms →
      InvA M y y' L (1 + d) ((sim M).run (pairInf y y') (4 * d + (5 + (1 + 5 * ms)))) := by
    intro d
    induction d with
    | zero => intro _; simpa using hA1
    | succ d ih =>
      intro hd
      rw [show 4 * (d + 1) + (5 + (1 + 5 * ms)) = 4 + (4 * d + (5 + (1 + 5 * ms))) by ring,
        run_add, show 1 + (d + 1) = (1 + d) + 1 by ring]
      exact A_iter M y y' L (1 + d) _ (ih (by omega)) (by omega) (by omega)
  have hfin := hA (ms - 1) (by omega)
  rw [show 1 + (ms - 1) = ms by omega] at hfin
  have hex := A_exit M y y' L ms _ hfin (by omega)
  rw [← run_add] at hex
  refine ⟨_, by omega, _, hex, ?_⟩
  obtain ⟨-, -, -, h0, -, hlow, -, hev⟩ := hfin
  intro k
  rcases k with _ | j
  · rw [consInf_apply, if_pos rfl]; simpa using h0
  · rw [consInf_apply, if_neg (by omega), show j + 1 - 1 = j by omega,
      show 2 * (j + 1) = 2 * j + 2 by ring]
    by_cases hj : j < ms
    · exact hlow j hj
    · rw [hev j (by omega)]
      have hy : y j = 0 := by
        by_contra hy
        have := lt_lengthInf (x := pairInf y y') (i := 2 * j) (by rw [pair_even]; exact hy)
        omega
      have hy' : y' j = 0 := by
        by_contra hy
        have := lt_lengthInf (x := pairInf y y') (i := 2 * j + 1) (by rw [pair_odd]; exact hy)
        omega
      rw [hy, hy']; split_ifs <;> rfl

end pre

/-! ### Correctness of the simulation on admissible inputs -/

lemma pair_zero_len (y : Rinf ℝ) : lengthInf (pairInf y 0) ≤ 2 * lengthInf y := by
  have h1 := one_le_lengthInf y
  apply lengthInf_le (by omega)
  intro i hi
  rw [pair_apply] at hi
  split_ifs at hi with he
  · have := lt_lengthInf hi; omega
  · exact absurd rfl hi

lemma key (y y' : Rinf ℝ) (hM : M.Halts y) :
    ∃ T, (sim M).HaltsBy (pairInf y y') T ∧
      (sim M).outputVal (pairInf y y') = M.outputVal y ∧
      T ≤ 2 * M.haltingTime y + (5 * lengthInf (pairInf y y') + 10) := by
  have h0 : M.HaltsBy y (M.haltingTime y) := Nat.sInf_mem hM
  obtain ⟨T, hT, X, hrun, hX⟩ := pre_spec M y y'
  have hrel : Rel M (M.entry, 0, 0, consInf ((lengthInf y : ℕ) : ℝ) y)
      (simIdx M M.entry, 0, 0, X) := ⟨rfl, rfl, rfl, hX⟩
  obtain ⟨s, hs, hr⟩ := sim_run M _ _ hrel (M.haltingTime y)
  have e1 : M.step^[M.haltingTime y] (M.entry, 0, 0, consInf ((lengthInf y : ℕ) : ℝ) y) =
      M.run y (M.haltingTime y) := rfl
  have e2 : (sim M).step^[s] (simIdx M M.entry, 0, 0, X) = (sim M).run (pairInf y y') (s + T) := by
    rw [run_add, hrun]
  rw [e1, e2] at hr
  have hh : (sim M).HaltsBy (pairInf y y') (s + T) := rel_output M hr h0
  refine ⟨s + T, hh, ?_, by omega⟩
  unfold Machine.outputVal
  rw [(halting_spec hh).2, (halting_spec h0).2]
  have := hr.2.2.2 0
  simpa using this

end
end PNP

theorem decisionInNP_of_decisionInP (Y Yyes : Set (Rinf ℝ)) (hsub : Yyes ⊆ Y)
    (hP : DecisionInP Y Yyes) : DecisionInNP Y Yyes := by
  obtain ⟨M, hsol, c, q, hcl⟩ := hP
  refine ⟨PNP.sim M, 2 * c + 30, q + 1, ?_, ?_, ?_⟩
  · intro y hy y' _
    obtain ⟨T, -, hout, -⟩ := PNP.key M y y' (hsol y hy).1
    rw [hout]; exact (hsol y hy).2.1
  · intro y hy y' _ h1
    obtain ⟨T, -, hout, -⟩ := PNP.key M y y' (hsol y hy).1
    rw [hout] at h1; exact (hsol y hy).2.2.mp h1
  · intro y hy
    have hY := hsub hy
    obtain ⟨T, hh, hout, hT⟩ := PNP.key M y 0 (hsol y hY).1
    refine ⟨0, ⟨T, hh⟩, by rw [hout]; exact (hsol y hY).2.2.mpr hy, ?_⟩
    have hle := (PNP.halting_spec hh).1
    have ht := (hcl y hY).2
    have hL := PNP.pair_zero_len y
    have hS : 2 ≤ sizeR y := by have := PNP.one_le_lengthInf y; unfold sizeR; omega
    have hsz : sizeR y = lengthInf y + 1 := rfl
    have hp1 : sizeR y ^ q ≤ sizeR y ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : sizeR y ≤ sizeR y ^ (q + 1) := by
      calc sizeR y = sizeR y ^ 1 := (pow_one _).symm
        _ ≤ sizeR y ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hc1 : c * sizeR y ^ q ≤ c * sizeR y ^ (q + 1) := Nat.mul_le_mul_left c hp1
    nlinarith

end BSS

namespace BSS

theorem _root_.solution (Y Yyes : Set (Rinf ℝ)) (hsub : Yyes ⊆ Y) (hP : DecisionInP Y Yyes) :
    DecisionInNP Y Yyes :=
  BSS.decisionInNP_of_decisionInP Y Yyes hsub hP

end BSS
