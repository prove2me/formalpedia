-- Prove2me | solution 1 for BicliqueSDP.Chain.relations_40_41
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:37:46.06289+00:00
-- url     : https://prove2.me/submissions/2852977c-1d3e-404e-bf5a-4f1310c513d4

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.RelationsProof

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

lemma frob_smul_right {ι : Type} [Fintype ι] (a : ℝ) (M X : Matrix ι ι ℝ) :
    frob M (a • X) = a * frob M X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

lemma psd_objective_le_trace_mul_h1 (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hp : X.PosSemidef)
    (hE : VanishesOnEdges E X) :
    frob Cmat X ≤ X.trace * h1 E := by
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · have hz : X = 0 := hp.trace_eq_zero_iff.mp ht.symm
    simp [hz, frob]
  · have hnorm : H1Feasible E (X.trace⁻¹ • X) := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro u v huv
        simp [hE u v huv]
    have hle := le_csSup (h1_objective_bddAbove E) ⟨X.trace⁻¹ • X, hnorm, rfl⟩
    change frob Cmat (X.trace⁻¹ • X) ≤ h1 E at hle
    rw [frob_smul_right] at hle
    have := (div_le_iff₀ ht).mp (show frob Cmat X / X.trace ≤ h1 E by
      simpa [div_eq_mul_inv, mul_comm] using hle)
    simpa [mul_comm] using this

section Perturbation
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def coordScale (k : ι) (t : ℝ) (i : ι) : ℝ := if i = k then 1 + t else 1

def perturb (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (coordScale k t) * X * Matrix.diagonal (coordScale k t)

lemma perturb_apply (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) (i j : ι) :
    perturb X k t i j = coordScale k t i * X i j * coordScale k t j := by
  simp [perturb, Matrix.diagonal_mul, Matrix.mul_diagonal]

lemma perturb_psd {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (k : ι) (t : ℝ) :
    (perturb X k t).PosSemidef := by
  simpa [perturb] using hX.mul_mul_conjTranspose_same (Matrix.diagonal (coordScale k t))

lemma perturb_trace (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) :
    (perturb X k t).trace = X.trace + (2 * t + t ^ 2) * X k k := by
  have he (i : ι) : perturb X k t i i =
      X i i + if i = k then (2 * t + t ^ 2) * X k k else 0 := by
    by_cases hi : i = k
    · subst i
      simp [perturb_apply, coordScale]
      ring
    · simp [perturb_apply, coordScale, hi]
  simp only [Matrix.trace, Matrix.diag, he, Finset.sum_add_distrib]
  simp

lemma perturb_frob (C X : Matrix ι ι ℝ) (k : ι) (t : ℝ)
    (hC : C.IsSymm) (hX : X.IsSymm) (hdiag : C k k = 0) :
    frob C (perturb X k t) = frob C X + 2 * t * (∑ j, C k j * X k j) := by
  have he (i j : ι) : C i j * perturb X k t i j = C i j * X i j +
      (if i = k then t * (C i j * X i j) else 0) +
      (if j = k then t * (C i j * X i j) else 0) := by
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j
      simp [hdiag]
    · simp [perturb_apply, coordScale, hi, hj]
      ring
    · simp [perturb_apply, coordScale, hi, hj]
      ring
    · simp [perturb_apply, coordScale, hi, hj]
  simp only [frob, he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  have hs : (∑ i, t * (C i k * X i k)) = ∑ i, t * (C k i * X k i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← hC.apply i k, ← hX.apply i k]
  rw [hs]
  rw [← Finset.mul_sum]
  ring

end Perturbation

lemma optimal_weighted_row (E : V1 → V2 → Prop)
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hopt : frob Cmat X = h1 E) (k : V1 ⊕ V2) :
    (∑ j, Cmat k j * X k j) = h1 E * X k k := by
  have hC : (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ).IsSymm := by
    ext i j
    cases i <;> cases j <;> simp [Cmat, Matrix.fromBlocks, Matrix.transpose_apply]
  have hS : X.IsSymm := Matrix.isHermitian_iff_isSymm.mp hX.1.isHermitian
  have hdiag : (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) k k = 0 := by
    cases k <;> simp [Cmat, Matrix.fromBlocks]
  have hq (t : ℝ) : 0 ≤ (h1 E * X k k) * (t * t) +
      (2 * h1 E * X k k - 2 * ∑ j, Cmat k j * X k j) * t + 0 := by
    have hE : VanishesOnEdges E (perturb X k t) := by
      intro u v huv
      simp [perturb_apply, hX.2.2 u v huv]
    have hle := psd_objective_le_trace_mul_h1 E (perturb_psd hX.1 k t) hE
    rw [perturb_trace, perturb_frob Cmat X k t hC hS hdiag, hX.2.1, hopt] at hle
    nlinarith
  have hd := discrim_le_zero hq
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (2 * h1 E * X k k - 2 * ∑ j, Cmat k j * X k j)]

end
end BicliqueSDP.Chain.RelationsProof


open BicliqueSDP.Chain BicliqueSDP.Chain.RelationsProof in
/-- Relations (40) and (41) follow from coordinate scaling at an optimal primal matrix. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hopt : frob Cmat X = h1 E) :
    (∀ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) = 2 * h1 E * X (Sum.inl i) (Sum.inl i)) ∧
    (∀ j : V2, ∑ i : V1, X (Sum.inr j) (Sum.inl i) = 2 * h1 E * X (Sum.inr j) (Sum.inr j)) := by
  constructor
  · intro i
    have hi := optimal_weighted_row E X hX hopt (Sum.inl i)
    simp [Cmat, Matrix.fromBlocks, ← Finset.mul_sum] at hi
    linarith
  · intro j
    have hj := optimal_weighted_row E X hX hopt (Sum.inr j)
    simp [Cmat, Matrix.fromBlocks, ← Finset.mul_sum] at hj
    linarith
