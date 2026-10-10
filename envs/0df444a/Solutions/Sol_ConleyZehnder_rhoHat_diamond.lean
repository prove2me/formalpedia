-- Prove2me | solution 1 for ConleyZehnder.rhoHat_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:15:57.550105+00:00
-- url     : https://prove2.me/submissions/bff2c34a-a529-41f3-a243-0fe5c00ee8fa

import Definitions.Def_ConleyZehnder_Setting

open ConleyZehnder Matrix

namespace CZ16A

variable {n : ℕ}

/-- The complex matrix `X + iY` whose determinant is `complexLinearDet`. -/
noncomputable def cxm (M : Mat n) : Matrix (Fin n) (Fin n) ℂ :=
  (complexLinearPart M).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
    Complex.I • (complexLinearPart M).toBlocks₂₁.map (fun x : ℝ => (x : ℂ))

theorem cxm_apply (M : Mat n) (i j : Fin n) :
    cxm M i j = ((M (Sum.inl i) (Sum.inl j) + M (Sum.inr i) (Sum.inr j) : ℝ) : ℂ) / 2 +
      Complex.I * (((M (Sum.inr i) (Sum.inl j) - M (Sum.inl i) (Sum.inr j) : ℝ) : ℂ) / 2) := by
  have h11 : (complexLinearPart M).toBlocks₁₁ i j =
      (M (Sum.inl i) (Sum.inl j) + M (Sum.inr i) (Sum.inr j)) / 2 := by
    simp [complexLinearPart, toBlocks₁₁, Matrix.J, mul_apply, Fintype.sum_sum_type, fromBlocks,
      one_apply]
    ring
  have h21 : (complexLinearPart M).toBlocks₂₁ i j =
      (M (Sum.inr i) (Sum.inl j) - M (Sum.inl i) (Sum.inr j)) / 2 := by
    simp [complexLinearPart, toBlocks₂₁, Matrix.J, mul_apply, Fintype.sum_sum_type, fromBlocks,
      one_apply]
    ring
  simp only [cxm, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h11, h21]
  push_cast; ring

theorem cxm_diamond {n' n'' : ℕ} (A : Mat n') (B : Mat n'') :
    (cxm (diamond A B)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (cxm A) 0 0 (cxm B) := by
  ext (a | b) (c | d) <;>
    simp [cxm_apply, diamond, reindex_apply, submatrix_apply, fromBlocks]

end CZ16A

open CZ16A

theorem solution {n' n'' : ℕ} (A : Mat n') (B : Mat n'') :
    complexLinearDet (diamond A B) = complexLinearDet A * complexLinearDet B ∧
      rhoHat (diamond A B) = rhoHat A * rhoHat B := by
  have hdet : complexLinearDet (diamond A B) = complexLinearDet A * complexLinearDet B := by
    show (cxm (diamond A B)).det = (cxm A).det * (cxm B).det
    rw [← det_submatrix_equiv_self finSumFinEquiv, cxm_diamond, det_fromBlocks_zero₂₁]
  refine ⟨hdet, ?_⟩
  unfold rhoHat
  rw [hdet, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
