-- Prove2me | solution 1 for BicliqueSDP.Chain.sqrt_g_le_h1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:31:35.91093+00:00
-- url     : https://prove2.me/submissions/6a54e070-ddcd-4ec8-8910-c6d4746655cc

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.SqrtGProof

noncomputable section

lemma psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

lemma psd_entry_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    X i j ≤ 1 := by
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc X k k ≤ ∑ l, X l l := Finset.single_le_sum (f := fun l => X l l) (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
         _ = 1 := htr
  have hpair := psd_entry_le_diag_avg hX i j
  linarith [hdiag i, hdiag j]

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

lemma h1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | H1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_one hX.1 hX.2.1 u v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

lemma h1_nonneg (E : V1 → V2 → Prop) : 0 ≤ h1 E := by
  classical
  by_cases hn : Nonempty (V1 ⊕ V2)
  · obtain ⟨u⟩ := hn
    let X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ := Matrix.diagonal (Pi.single u 1)
    have hX : H1Feasible E X := by
      refine ⟨Matrix.PosSemidef.diagonal ?_, ?_, ?_⟩
      · intro v
        simp only [Pi.single_apply]
        split <;> norm_num
      · simp [X, Matrix.trace_diagonal]
      · intro v w hvw
        exact Matrix.diagonal_apply_ne _ hvw.ne
    have hobj : frob Cmat X = 0 := by
      simp [frob, X, Matrix.diagonal, Cmat, Matrix.fromBlocks]
    rw [← hobj]
    exact le_csSup (h1_objective_bddAbove E) ⟨X, hX, rfl⟩
  · have : IsEmpty (V1 ⊕ V2) := not_nonempty_iff.mp hn
    have he : {X | H1Feasible E X} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro X hX
      have ht : X.trace = 0 := by simp [Matrix.trace]
      exact zero_ne_one (ht.symm.trans hX.2.1)
    simp [h1, he]

def pairVector (A : Finset V1) (B : Finset V2) (x y : ℝ) : V1 ⊕ V2 → ℝ :=
  Sum.elim (fun i => if i ∈ A then x else 0) (fun j => if j ∈ B then y else 0)

lemma pairVector_trace (A : Finset V1) (B : Finset V2) (x y : ℝ) :
    (vecMulVec (pairVector A B x y) (pairVector A B x y)).trace =
      A.card * x ^ 2 + B.card * y ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec, pairVector,
    Fintype.sum_sum_type, ← pow_two]

lemma pairVector_frob (A : Finset V1) (B : Finset V2) (x y : ℝ) :
    frob Cmat (vecMulVec (pairVector A B x y) (pairVector A B x y)) =
      A.card * B.card * x * y := by
  simp [frob, Cmat, Matrix.vecMulVec, pairVector, Fintype.sum_sum_type,
    Matrix.fromBlocks]
  ring

lemma pairVector_psd (A : Finset V1) (B : Finset V2) (x y : ℝ) :
    (vecMulVec (pairVector A B x y) (pairVector A B x y)).PosSemidef := by
  simpa using Matrix.posSemidef_vecMulVec_self_star (pairVector A B x y)

omit [Fintype V1] [Fintype V2] in
lemma pairVector_vanishes (E : V1 → V2 → Prop) (A : Finset V1) (B : Finset V2)
    (hAB : IsBiindep E A B) (x y : ℝ) :
    VanishesOnEdges E (vecMulVec (pairVector A B x y) (pairVector A B x y)) := by
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => exact False.elim huv
    | inr j =>
      by_cases hi : i ∈ A
      · have hj : j ∉ B := fun hj => hAB i hi j hj huv
        simp [Matrix.vecMulVec, pairVector, hj]
      · simp [Matrix.vecMulVec, pairVector, hi]
  | inr j =>
    cases v with
    | inl i =>
      by_cases hi : i ∈ A
      · have hj : j ∉ B := fun hj => hAB i hi j hj huv
        simp [Matrix.vecMulVec, pairVector, hj]
      · simp [Matrix.vecMulVec, pairVector, hi]
    | inr i => exact False.elim huv

omit [DecidableEq V1] [DecidableEq V2] in
lemma frob_smul (M X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (c : ℝ) :
    frob M (c • X) = c * frob M X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

lemma pair_witness (E : V1 → V2 → Prop) (A : Finset V1) (B : Finset V2)
    (hAB : IsBiindep E A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ X, H1Feasible E X ∧ frob Cmat X = (1 / 2) * Real.sqrt ((A.card : ℝ) * B.card) := by
  let a : ℝ := A.card
  let b : ℝ := B.card
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hA.card_pos
  have hb : 0 < b := by dsimp [b]; exact_mod_cast hB.card_pos
  let v := pairVector A B (Real.sqrt b) (Real.sqrt a)
  let X := (2 * a * b)⁻¹ • vecMulVec v v
  refine ⟨X, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (pairVector_psd A B _ _).smul (by positivity : 0 ≤ (2 * a * b)⁻¹)
  · change ((2 * a * b)⁻¹ • vecMulVec v v).trace = 1
    rw [Matrix.trace_smul]
    change (2 * a * b)⁻¹ * (vecMulVec v v).trace = 1
    rw [pairVector_trace]
    rw [Real.sq_sqrt hb.le, Real.sq_sqrt ha.le]
    change (2 * a * b)⁻¹ * (a * b + b * a) = 1
    field_simp
    ring
  · intro u w huw
    change (2 * a * b)⁻¹ * (vecMulVec v v) u w = 0
    rw [pairVector_vanishes E A B hAB _ _ u w huw, mul_zero]
  · change frob Cmat ((2 * a * b)⁻¹ • vecMulVec v v) = _
    rw [frob_smul, pairVector_frob]
    rw [Real.sqrt_mul ha.le]
    change (2 * a * b)⁻¹ * (a * b * Real.sqrt b * Real.sqrt a) =
      (1 / 2) * (Real.sqrt a * Real.sqrt b)
    field_simp

end
end BicliqueSDP.Chain.SqrtGProof

/-- The primal rank-one construction proves the bound, including empty vertex types. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    (1 / 2) * Real.sqrt (BicliqueSDP.Chain.g E) ≤ BicliqueSDP.Chain.h1 E := by
  classical
  open BicliqueSDP.Chain BicliqueSDP.Chain.SqrtGProof in
  obtain ⟨⟨A, B⟩, hp, hg⟩ := (pairs E).exists_mem_eq_sup'
    ⟨_, empty_mem_pairs E⟩ (fun p => (p.1.card : ℝ) * p.2.card)
  change BicliqueSDP.Chain.g E = (A.card : ℝ) * B.card at hg
  rw [hg]
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hAB := (Finset.mem_filter.mp hp).2
      obtain ⟨X, hX, hv⟩ := BicliqueSDP.Chain.SqrtGProof.pair_witness E A B hAB hA hB
      rw [← hv]
      exact le_csSup (BicliqueSDP.Chain.SqrtGProof.h1_objective_bddAbove E) ⟨X, hX, rfl⟩
    · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      simpa [he] using BicliqueSDP.Chain.SqrtGProof.h1_nonneg E
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simpa [he] using BicliqueSDP.Chain.SqrtGProof.h1_nonneg E
