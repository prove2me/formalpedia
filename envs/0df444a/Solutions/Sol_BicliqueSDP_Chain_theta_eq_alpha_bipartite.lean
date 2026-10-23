-- Prove2me | solution 1 for BicliqueSDP.Chain.theta_eq_alpha_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:43:28.60602+00:00
-- url     : https://prove2.me/submissions/a6433c2f-69f9-4553-b1aa-0f1b17627cf7

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain.ThetaProof

open Matrix

noncomputable section

private theorem entry_le_diag_avg {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hX : X.PosSemidef) (i j : V) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

theorem sum_le_card_mul_trace {V : Type*} [Fintype V]
    (X : Matrix V V ℝ) (hX : X.PosSemidef) :
    (∑ i, ∑ j, X i j) ≤ (Fintype.card V : ℝ) * X.trace := by
  classical
  calc
    (∑ i, ∑ j, X i j) ≤ ∑ i, ∑ j, (X i i + X j j) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry_le_diag_avg hX i j
    _ = (Fintype.card V : ℝ) * X.trace := by
      simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
        Matrix.trace, Matrix.diag]
      ring

private def coverMatrix {V K : Type*} [DecidableEq K] (c : V → K) : Matrix K V ℝ :=
  fun k i => if c i = k then 1 else 0

private theorem sum_fibers {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    (c : V → K) (f : V → ℝ) :
    (∑ k, ∑ i, if c i = k then f i else 0) = ∑ i, f i := by
  rw [Finset.sum_comm]
  simp

private theorem collapse_apply {V K : Type*} [Fintype V] [DecidableEq K]
    (c : V → K) (X : Matrix V V ℝ) (k l : K) :
    (coverMatrix c * X * (coverMatrix c)ᴴ) k l =
      ∑ i, ∑ j, if c i = k ∧ c j = l then X i j else 0 := by
  simp only [Matrix.mul_apply, coverMatrix, Matrix.conjTranspose_apply,
    star_trivial, mul_ite, ite_mul,
    one_mul, mul_one, zero_mul, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = l <;> simp [h]

private theorem collapse_sum {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    (c : V → K) (X : Matrix V V ℝ) :
    (∑ k, ∑ l, (coverMatrix c * X * (coverMatrix c)ᴴ) k l) =
      ∑ i, ∑ j, X i j := by
  simp only [collapse_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  simp only [sum_fibers]
  rw [Finset.sum_comm]
  simp only [sum_fibers]

private theorem collapse_trace {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    (c : V → K) (X : Matrix V V ℝ)
    (hclique : ∀ i j, i ≠ j → c i = c j → X i j = 0) :
    (coverMatrix c * X * (coverMatrix c)ᴴ).trace = X.trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, collapse_apply]
  have hinner (k : K) (i : V) :
      (∑ j, if c i = k ∧ c j = k then X i j else 0) =
        if c i = k then X i i else 0 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      split_ifs with h
      · exact hclique i j (Ne.symm hji) (h.1.trans h.2.symm)
      · rfl
    · simp
  simp_rw [hinner]
  rw [Finset.sum_comm]
  simp

/-- A clique partition with `K` labels bounds a PSD matrix's total entry sum by
the number of labels times its trace, when off-diagonal entries within a clique vanish. -/
theorem sum_le_card_mul_trace_of_clique_cover {V K : Type*} [Fintype V] [Fintype K]
    (c : V → K) (X : Matrix V V ℝ) (hX : X.PosSemidef)
    (hclique : ∀ i j, i ≠ j → c i = c j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ (Fintype.card K : ℝ) * X.trace := by
  classical
  have hY := hX.mul_mul_conjTranspose_same (coverMatrix c)
  have hsum := sum_le_card_mul_trace _ hY
  rwa [collapse_sum, collapse_trace c X hclique] at hsum

end

end BicliqueSDP.Chain.ThetaProof

namespace BicliqueSDP.Chain.ThetaProof

noncomputable section

variable {V1 V2 : Type} [Fintype V1] [Fintype V2]
  [DecidableEq V1] [DecidableEq V2]

omit [Fintype V1] in
/-- A bound on the sizes of biindependent pairs supplies enough dummy vertices
to make the Hall condition hold on the left part. -/
theorem exists_hall_assignment (E : V1 → V2 → Prop) (a : ℕ)
    (hbound : ∀ A B, IsBiindep E A B → A.card + B.card ≤ a) :
    ∃ f : V1 → V2 ⊕ Fin (a - Fintype.card V2), Function.Injective f ∧
      ∀ i, Sum.elim (E i) (fun _ => True) (f i) := by
  classical
  let R : V1 → V2 ⊕ Fin (a - Fintype.card V2) → Prop :=
    fun i => Sum.elim (E i) (fun _ => True)
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  let N : Finset V2 := Finset.univ.filter (fun j => ∃ i ∈ S, E i j)
  have hB : IsBiindep E S Nᶜ := by
    intro i hi j hj hij
    have hjN : j ∈ N := by simp [N]; exact ⟨i, hi, hij⟩
    exact (Finset.mem_compl.mp hj) hjN
  have hsize := hbound S Nᶜ hB
  have hNcard : N.card ≤ Fintype.card V2 := Finset.card_le_univ N
  have hright : Fintype.card V2 ≤ a := by
    simpa using hbound ∅ Finset.univ (by simp [IsBiindep])
  have hneigh : (Finset.univ.filter (fun b => ∃ i ∈ S, R i b)) =
      N.disjSum (Finset.univ : Finset (Fin (a - Fintype.card V2))) := by
    ext b
    cases b with
    | inl j => simp [R, N]
    | inr k =>
      simp [R]
      obtain ⟨i, hi⟩ := hSne
      exact ⟨i, hi⟩
  rw [hneigh, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_compl] at hsize
  omega

omit [Fintype V1] in
/-- A finite bipartite graph admits a partition into cliques using at most the
maximum permitted size of a biindependent pair. -/
theorem exists_clique_cover (E : V1 → V2 → Prop) (a : ℕ)
    (hbound : ∀ A B, IsBiindep E A B → A.card + B.card ≤ a) :
    ∃ c : V1 ⊕ V2 → V2 ⊕ Fin (a - Fintype.card V2),
      ∀ u v, u ≠ v → c u = c v → (bipGraph E).Adj u v := by
  obtain ⟨f, hf, hE⟩ := exists_hall_assignment E a hbound
  refine ⟨Sum.elim f Sum.inl, ?_⟩
  intro u v huv hcol
  cases u with
  | inl i =>
    cases v with
    | inl i' => exact (huv (congrArg Sum.inl (hf hcol))).elim
    | inr j =>
      change f i = Sum.inl j at hcol
      have := hE i
      simpa [hcol, bipGraph] using this
  | inr j =>
    cases v with
    | inl i =>
      change Sum.inl j = f i at hcol
      have := hE i
      simpa [← hcol, bipGraph] using this
    | inr j' => exact (huv (congrArg Sum.inr (Sum.inl.inj hcol))).elim

/-- The finite maximum defining alpha is the cast of a natural number, and it
bounds the cardinality of every biindependent pair. -/
theorem exists_nat_alpha (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    ∃ a : ℕ, alpha E = (a : ℝ) ∧
      ∀ A B, IsBiindep E A B → A.card + B.card ≤ a := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := pairs E) ⟨_, empty_mem_pairs E⟩
    (fun p : Finset V1 × Finset V2 => (p.1.card : ℝ) + p.2.card)
  have hα : alpha E = ((p.1.card + p.2.card : ℕ) : ℝ) := by
    simpa [alpha] using hmax
  refine ⟨p.1.card + p.2.card, hα, ?_⟩
  intro A B hAB
  have hmem : (A, B) ∈ pairs E := by simp [pairs, hAB]
  have hle : (A.card : ℝ) + B.card ≤ alpha E :=
    Finset.le_sup' (f := fun p : Finset V1 × Finset V2 =>
      (p.1.card : ℝ) + p.2.card) hmem
  rw [hα] at hle
  exact_mod_cast hle

end

end BicliqueSDP.Chain.ThetaProof

namespace BicliqueSDP.Chain.ThetaProof

open Matrix

noncomputable section

theorem theta_objective_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove ((fun X : Matrix V V ℝ => ∑ i, ∑ j, X i j) ''
      {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro z ⟨X, hX, rfl⟩
  simpa [hX.2.1] using sum_le_card_mul_trace X hX.1

theorem theta_nonneg {V : Type} [Fintype V] (G : SimpleGraph V) : 0 ≤ theta G := by
  apply Real.sSup_nonneg
  rintro z ⟨X, hX, rfl⟩
  simpa [dotProduct, mulVec] using hX.1.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))

/-- The normalized outer product of an independent-set indicator is theta-feasible. -/
theorem card_le_theta_of_independent {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ i ∈ S, ∀ j ∈ S, ¬G.Adj i j) : (S.card : ℝ) ≤ theta G := by
  classical
  by_cases hn : S.card = 0
  · simpa [hn] using theta_nonneg G
  have hnR : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let x : V → ℝ := fun i => if i ∈ S then 1 else 0
  let X : Matrix V V ℝ := (S.card : ℝ)⁻¹ • vecMulVec x x
  have hpsd : X.PosSemidef := by
    have hx : (vecMulVec x x).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star x
    exact hx.smul (inv_nonneg.mpr (Nat.cast_nonneg S.card))
  have htrace : X.trace = 1 := by
    simp [X, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct, x, hnR]
  have hedge : ∀ i j, G.Adj i j → X i j = 0 := by
    intro i j hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := fun hj => hS i hi j hj hij
      simp [X, Matrix.vecMulVec, x, hi, hj]
    · simp [X, Matrix.vecMulVec, x, hi]
  have hsum : (∑ i, ∑ j, X i j) = (S.card : ℝ) := by
    simp [X, Matrix.vecMulVec, x, hnR]
  rw [← hsum]
  exact le_csSup (theta_objective_bddAbove G) ⟨X, ⟨hpsd, htrace, hedge⟩, rfl⟩

theorem biindep_card_le_theta {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    (A : Finset V1) (B : Finset V2) (hAB : IsBiindep E A B) :
    (A.card : ℝ) + B.card ≤ theta (bipGraph E) := by
  have := card_le_theta_of_independent (bipGraph E) (A.disjSum B) (by
    intro u hu v hv
    cases u <;> cases v <;> simp_all [bipGraph, IsBiindep])
  simpa [Finset.card_disjSum] using this

end

end BicliqueSDP.Chain.ThetaProof

namespace BicliqueSDP.Chain.ThetaProof

open Matrix

noncomputable section

variable {V1 V2 : Type} [Fintype V1] [Fintype V2]
  [DecidableEq V1] [DecidableEq V2]

/-- Hall's clique partition bounds every feasible theta objective by alpha. -/
theorem theta_objective_le_alpha (E : V1 → V2 → Prop)
    [∀ i j, Decidable (E i j)] (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : H1Feasible E X) : (∑ i, ∑ j, X i j) ≤ alpha E := by
  obtain ⟨a, hα, hbound⟩ := exists_nat_alpha E
  obtain ⟨c, hc⟩ := exists_clique_cover E a hbound
  have hright : Fintype.card V2 ≤ a := by
    simpa using hbound ∅ Finset.univ (by simp [IsBiindep])
  have hK : Fintype.card (V2 ⊕ Fin (a - Fintype.card V2)) = a := by
    simp [Nat.add_sub_of_le hright]
  calc
    (∑ i, ∑ j, X i j) ≤
        (Fintype.card (V2 ⊕ Fin (a - Fintype.card V2)) : ℝ) * X.trace :=
      sum_le_card_mul_trace_of_clique_cover c X hX.1
        (fun i j hne heq => hX.2.2 i j (hc i j hne heq))
    _ = alpha E := by rw [hK, hX.2.1, mul_one]; exact hα.symm

theorem theta_le_alpha (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    theta (bipGraph E) ≤ alpha E := by
  unfold theta
  by_cases hne : ((fun X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ => ∑ i, ∑ j, X i j) ''
      {X | X.PosSemidef ∧ X.trace = 1 ∧
        ∀ i j, (bipGraph E).Adj i j → X i j = 0}).Nonempty
  · apply csSup_le hne
    rintro z ⟨X, hX, rfl⟩
    exact theta_objective_le_alpha E X hX
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    obtain ⟨a, hα, _⟩ := exists_nat_alpha E
    rw [hα]
    positivity

theorem alpha_le_theta (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    alpha E ≤ theta (bipGraph E) := by
  unfold alpha
  apply Finset.sup'_le
  intro p hp
  exact biindep_card_le_theta E p.1 p.2 (Finset.mem_filter.mp hp).2

end

end BicliqueSDP.Chain.ThetaProof

open BicliqueSDP.Chain

/-- The theta number of a finite bipartite graph equals its stability number. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1]
    [DecidableEq V2] (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    theta (bipGraph E) = alpha E := by
  exact le_antisymm (ThetaProof.theta_le_alpha E) (ThetaProof.alpha_le_theta E)
