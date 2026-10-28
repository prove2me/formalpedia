-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inverse_quadratic_young_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:49.286596+00:00
-- url     : https://prove2.me/submissions/eddfdf72-126b-44dc-90e2-473916456185

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

noncomputable section
open scoped MatrixOrder Kronecker
section InverseYoung
open scoped BigOperators Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The inverse-quadratic Young inequality for a finite real positive-definite matrix. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) ≤ v ⬝ᵥ (H⁻¹ *ᵥ v) + w ⬝ᵥ (H *ᵥ w) := by
  classical
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hmul : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hcancel : H *ᵥ (H⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hmul]
    simp
  have hsymm : H.IsSymm := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have htranspose : Hᵀ = H := hsymm
  have hcross₁ : w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) = v ⬝ᵥ w := by
    rw [hcancel]
    exact dotProduct_comm _ _
  have hcross₂ : (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ w := by
    calc
      (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) =
          (H⁻¹ *ᵥ v) ⬝ᵥ (Hᵀ *ᵥ w) := by rw [htranspose]
      _ = w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) :=
        Matrix.dotProduct_transpose_mulVec H (H⁻¹ *ᵥ v) w
      _ = v ⬝ᵥ w := hcross₁
  have hlast : (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) =
      v ⬝ᵥ (H⁻¹ *ᵥ v) := by
    rw [hcancel]
    exact dotProduct_comm _ _
  have hquad :
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) =
        w ⬝ᵥ (H *ᵥ w) - 2 * (v ⬝ᵥ w) + v ⬝ᵥ (H⁻¹ *ᵥ v) := by
    calc
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) =
          (w ⬝ᵥ (H *ᵥ w) - w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v))) -
            ((H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) -
              (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v))) := by
        simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
        ring
      _ = w ⬝ᵥ (H *ᵥ w) - 2 * (v ⬝ᵥ w) + v ⬝ᵥ (H⁻¹ *ᵥ v) := by
        rw [hcross₁, hcross₂, hlast]
        ring
  have hnonneg : 0 ≤
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg (w - H⁻¹ *ᵥ v)
  nlinarith [hquad, hnonneg]
