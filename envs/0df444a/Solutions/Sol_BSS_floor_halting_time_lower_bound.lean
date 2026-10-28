-- Prove2me | solution 1 for BSS.floor_halting_time_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:34:39.091592+00:00
-- url     : https://prove2.me/submissions/2121a868-eda8-4503-9b1a-1f86976e0772

import Definitions.Def_BSSFeasibility

namespace BSS
namespace FloorLB

open Polynomial

noncomputable section

/-! ### Generic facts about machines -/

lemma isOutput_iff {N : ℕ} (nd : Node ℝ N) : nd.IsOutput ↔ nd = Node.output := by
  cases nd <;> simp [Node.IsOutput]

lemma iterate_output {M : Machine ℝ} {c : M.Config} (h : (M.nodes c.1).IsOutput) (s : ℕ) :
    M.step^[s] c = c := by
  rw [isOutput_iff] at h
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold Machine.step; rw [h]

lemma run_add (M : Machine ℝ) (y : Rinf ℝ) (a b : ℕ) :
    M.run y (a + b) = M.step^[a] (M.run y b) := by
  unfold Machine.run; rw [Function.iterate_add_apply]

lemma output_of_le {M : Machine ℝ} {y : Rinf ℝ} (hM : M.Halts y) {n : ℕ}
    (hn : M.haltingTime y ≤ n) : M.output y = (M.run y n).2.2.2 := by
  have h0 : M.HaltsBy y (M.haltingTime y) := Nat.sInf_mem hM
  unfold Machine.output
  have : n = (n - M.haltingTime y) + M.haltingTime y := by omega
  rw [this, run_add, iterate_output h0]

lemma polyEval_apply (g : PolyMapInf ℝ) (x : Rinf ℝ) (i : ℕ) :
    g.eval x i = if h : i < g.dim then
      MvPolynomial.eval (fun j : Fin g.dim => x (j : ℕ)) (g.coord ⟨i, h⟩) else x i := by
  unfold PolyMapInf.eval; rw [Finsupp.onFinset_apply]

/-! ### Symbolic runs: along a fixed sequence of branch outcomes, every coordinate is a
polynomial in the input `x`. -/

structure SState (N : ℕ) where
  node : Fin N
  i : ℕ
  j : ℕ
  Q : ℕ → ℝ[X]

def toPoly {d : ℕ} (Q : ℕ → ℝ[X]) (p : MvPolynomial (Fin d) ℝ) : ℝ[X] :=
  MvPolynomial.aeval (fun v : Fin d => Q v) p

lemma eval_toPoly {d : ℕ} (Q : ℕ → ℝ[X]) (p : MvPolynomial (Fin d) ℝ) (x : ℝ) :
    (toPoly Q p).eval x = MvPolynomial.eval (fun v : Fin d => (Q v).eval x) p := by
  unfold toPoly
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

variable (M : Machine ℝ)

def symStep (b : Bool) (s : SState M.numNodes) : SState M.numNodes :=
  match M.nodes s.node with
  | .output => s
  | .computation g iOp jOp next =>
      ⟨next, iOp.apply s.i, jOp.apply s.j,
        fun k => if h : k < g.dim then toPoly s.Q (g.coord ⟨k, h⟩) else s.Q k⟩
  | .branch _ _ ng ps => ⟨if b then ng else ps, s.i, s.j, s.Q⟩
  | .fifth next => ⟨next, s.i, s.j, Function.update s.Q s.j (s.Q s.i)⟩

def outcome (c : M.Config) : Bool :=
  match M.nodes c.1 with
  | .branch _ h _ _ => decide (branchValue h c.2.2.2 < 0)
  | _ => false

def Corr (x : ℝ) (s : SState M.numNodes) (c : M.Config) : Prop :=
  c.1 = s.node ∧ c.2.1 = s.i ∧ c.2.2.1 = s.j ∧ ∀ k, c.2.2.2 k = (s.Q k).eval x

lemma corr_step (x : ℝ) (s : SState M.numNodes) (c : M.Config) (h : Corr M x s c) :
    Corr M x (symStep M (outcome M c) s) (M.step c) := by
  obtain ⟨a, i, j, X⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  cases hn : M.nodes s.node with
  | output =>
    simp only [symStep, Machine.step, hn]; exact ⟨rfl, rfl, rfl, h4⟩
  | computation g iOp jOp next =>
    simp only [symStep, Machine.step, hn]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro k
    simp only
    rw [polyEval_apply]
    split_ifs with hk
    · rw [eval_toPoly]
      have hf : (fun j : Fin g.dim => X (j : ℕ)) = fun v : Fin g.dim => (s.Q v).eval x := by
        funext v; exact h4 v
      rw [hf]
    · exact h4 k
  | branch k hp ng ps =>
    simp only [symStep, Machine.step, hn]
    refine ⟨?_, rfl, rfl, h4⟩
    simp only
    have ho : outcome M (s.node, s.i, s.j, X) = decide (branchValue hp X < 0) := by
      simp only [outcome, hn]
    rw [ho]
    by_cases hb : branchValue hp X < 0 <;> simp [hb]
  | fifth next =>
    simp only [symStep, Machine.step, hn]
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro k
    simp only [Finsupp.update_apply, Function.update_apply]
    split_ifs with hk
    · exact h4 _
    · exact h4 k

def symRun (s0 : SState M.numNodes) (σ : ℕ → Bool) : ℕ → SState M.numNodes
  | 0 => s0
  | n + 1 => symStep M (σ n) (symRun s0 σ n)

lemma symRun_congr (s0 : SState M.numNodes) (σ σ' : ℕ → Bool) (n : ℕ)
    (h : ∀ k < n, σ k = σ' k) : symRun M s0 σ n = symRun M s0 σ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [symRun]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

lemma corr_run (x : ℝ) (s0 : SState M.numNodes) (c0 : M.Config) (h : Corr M x s0 c0) (n : ℕ) :
    Corr M x (symRun M s0 (fun k => outcome M (M.step^[k] c0)) n) (M.step^[n] c0) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [symRun]
    rw [Function.iterate_succ_apply']
    exact corr_step M x _ _ ih

/-- The initial symbolic state for inputs `single 0 x`, `x ≠ 0`. -/
def Q0 : ℕ → ℝ[X] := fun k => if k = 0 then 1 else if k = 1 then X else 0

def s0 : SState M.numNodes := ⟨M.entry, 0, 0, Q0⟩

lemma lengthInf_single {x : ℝ} (hx : x ≠ 0) : lengthInf (Finsupp.single 0 x) = 1 := by
  unfold lengthInf
  have hs : (Finsupp.single (0 : ℕ) x).support = {0} := Finsupp.support_single_ne_zero 0 hx
  have hne : (Finsupp.single (0 : ℕ) x).support.Nonempty := by rw [hs]; simp
  rw [dif_pos hne]
  simp [hs]

lemma corr_init {x : ℝ} (hx : x ≠ 0) :
    Corr M x (s0 M) (M.entry, inputState (Finsupp.single 0 x)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k
  simp only [inputState, consInf, Finsupp.onFinset_apply, s0, Q0, lengthInf_single hx]
  rcases k with _ | _ | k
  · simp
  · simp
  · simp [Finsupp.single_apply]

def ext {m : ℕ} (τ : Fin m → Bool) : ℕ → Bool := fun s => if h : s < m then τ ⟨s, h⟩ else false

end
end FloorLB

open FloorLB in
theorem floor_halting_time_lower_bound (M : Machine ℝ)
    (hM : ∀ x : ℝ, 0 < x → M.Halts (Finsupp.single 0 x) ∧
      M.outputVal (Finsupp.single 0 x) = (⌊x⌋ : ℝ)) :
    ∀ L : ℝ, ∃ x : ℝ, L < x ∧
      Real.logb 2 x ≤ (M.haltingTime (Finsupp.single 0 x) : ℝ) := by
  intro L
  by_contra hcon
  push_neg at hcon
  -- parameters
  set A : ℕ := ⌊max L 1⌋₊ + 1 with hA
  have hA1 : (max L 1) < A := by rw [hA]; push_cast; exact Nat.lt_floor_add_one _
  have hLA : L < A := lt_of_le_of_lt (le_max_left _ _) hA1
  have h1A : (1 : ℝ) < A := lt_of_le_of_lt (le_max_right _ _) hA1
  -- classes of inputs
  let cls : ℝ → (Fin A → Bool) := fun x s =>
    outcome M (M.step^[s.val] (M.entry, inputState (Finsupp.single 0 x)))
  let K : Finset ℕ := Finset.Ico A (2 ^ (A + 1))
  -- every input of a unit interval in the range is computed along its class
  have key : ∀ k ∈ K, ∀ x : ℝ, (k : ℝ) ≤ x → x < k + 1 →
      ((symRun M (s0 M) (ext (cls x)) A).Q 0).eval x = k := by
    intro k hk x hx1 hx2
    have hkK := Finset.mem_Ico.mp hk
    have hx0 : 0 < x := by
      have : (1 : ℝ) < k := by
        have : (A : ℝ) ≤ k := by exact_mod_cast hkK.1
        linarith
      linarith
    obtain ⟨hhalt, hout⟩ := hM x hx0
    -- the halting time is at most m
    have hxt : x < (2 : ℝ) ^ ((A + 1 : ℕ) : ℝ) := by
      have : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (A + 1) := by exact_mod_cast hkK.2
      rw [Real.rpow_natCast]; linarith
    have hlog : Real.logb 2 x < ((A + 1 : ℕ) : ℝ) := (Real.logb_lt_iff_lt_rpow (by norm_num) hx0).2 hxt
    have hLx : L < x := by
      have : (A : ℝ) ≤ k := by exact_mod_cast hkK.1
      linarith
    have hT := hcon x hLx
    have hTm : M.haltingTime (Finsupp.single 0 x) ≤ A := by
      have : (M.haltingTime (Finsupp.single 0 x) : ℝ) < ((A + 1 : ℕ) : ℝ) := lt_trans hT hlog
      have : M.haltingTime (Finsupp.single 0 x) < A + 1 := by exact_mod_cast this
      omega
    have hc := corr_run M x (s0 M) _ (corr_init M hx0.ne') A
    have hsame : symRun M (s0 M) (ext (cls x)) A =
        symRun M (s0 M) (fun k => outcome M (M.step^[k] (M.entry, inputState (Finsupp.single 0 x)))) A := by
      apply symRun_congr
      intro s hs
      simp [ext, hs, cls]
    rw [hsame, ← hc.2.2.2 0]
    have : M.outputVal (Finsupp.single 0 x) =
        (M.step^[A] (M.entry, inputState (Finsupp.single 0 x))).2.2.2 0 := by
      unfold Machine.outputVal; rw [output_of_le hhalt hTm]; rfl
    rw [← this, hout]
    have hfl : ⌊x⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨hx1, hx2⟩
    rw [hfl]; simp
  -- choose, for each interval, a class with infinitely many members
  have hinf : ∀ k ∈ K, ∃ τ : Fin A → Bool,
      {x : ℝ | (k : ℝ) ≤ x ∧ x < k + 1 ∧ cls x = τ}.Infinite := by
    intro k hk
    by_contra hno
    push_neg at hno
    have hfin : (Set.Ico (k : ℝ) (k + 1)).Finite := by
      have : Set.Ico (k : ℝ) (k + 1) ⊆ ⋃ τ : Fin A → Bool,
          {x : ℝ | (k : ℝ) ≤ x ∧ x < k + 1 ∧ cls x = τ} := by
        intro x hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨cls x, hx.1, hx.2, rfl⟩
      exact Set.Finite.subset (Set.finite_iUnion fun τ => hno τ) this
    exact (Set.Ico_infinite (by linarith : (k : ℝ) < k + 1)) hfin
  choose! f hf using hinf
  have hcard : (Finset.univ : Finset (Fin A → Bool)).card < K.card := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      K, Nat.card_Ico]
    have h2 : A < 2 ^ A := Nat.lt_two_pow_self
    have h3 : 2 ^ (A + 1) = 2 * 2 ^ A := by ring
    omega
  obtain ⟨k1, hk1, k2, hk2, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  set τ := f k1 with hτ
  set p := (symRun M (s0 M) (ext τ) A).Q 0 with hp
  have hpk : ∀ k ∈ K, f k = τ → p = Polynomial.C (k : ℝ) := by
    intro k hk hfk
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono _ (hf k hk)
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    simp only [Set.mem_setOf_eq, Polynomial.eval_C]
    rw [hp, ← hfk, ← hx3]
    exact key k hk x hx1 hx2
  have e1 := hpk k1 hk1 rfl
  have e2 := hpk k2 hk2 heq.symm
  rw [e1] at e2
  have := Polynomial.C_injective e2
  exact hne (by exact_mod_cast this)

end BSS

namespace BSS

theorem _root_.solution (M : Machine ℝ)
    (hM : ∀ x : ℝ, 0 < x → M.Halts (Finsupp.single 0 x) ∧
      M.outputVal (Finsupp.single 0 x) = (⌊x⌋ : ℝ)) :
    ∀ L : ℝ, ∃ x : ℝ, L < x ∧
      Real.logb 2 x ≤ (M.haltingTime (Finsupp.single 0 x) : ℝ) :=
  BSS.floor_halting_time_lower_bound M hM

end BSS
