-- Prove2me | solution 1 for BosonicLearn.loewner_inv_form_le
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:58:53.791841+00:00
-- url     : https://prove2.me/submissions/ff62a959-a80c-496e-8e95-c8f6cff98f66

import Mathlib

open scoped Matrix

noncomputable section

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.PosDef) (α : ℝ) (hα : 0 < α) (hAB : (α • B - A).PosSemidef) (v : ι → ℝ) :
    v ⬝ᵥ (B⁻¹ *ᵥ v) ≤ α * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  set x : ι → ℝ := A⁻¹ *ᵥ v with hx
  set y : ι → ℝ := B⁻¹ *ᵥ v with hy
  have hAx : A *ᵥ x = v := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAdet, Matrix.one_mulVec]
  have hBy : B *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hBdet, Matrix.one_mulVec]
  have hAT : Aᵀ = A := by
    have h := hA.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- symmetry: x ⬝ A y = v ⬝ y
  have hsym : x ⬝ᵥ (A *ᵥ y) = v ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← hAT, Matrix.vecMul_transpose, hAx]
  -- positivity of A at w = x - α⁻¹ y
  have hpos := hA.posSemidef.dotProduct_mulVec_nonneg (x - α⁻¹ • y)
  have hstar : star (x - α⁻¹ • y) = x - α⁻¹ • y := by
    funext i
    simp
  rw [hstar] at hpos
  have hexp : (x - α⁻¹ • y) ⬝ᵥ (A *ᵥ (x - α⁻¹ • y)) =
      x ⬝ᵥ v - α⁻¹ * (v ⬝ᵥ y) - α⁻¹ * (y ⬝ᵥ v) + α⁻¹ * α⁻¹ * (y ⬝ᵥ (A *ᵥ y)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hAx, hsym]
    ring
  rw [hexp] at hpos
  -- the comparison A ⪯ α B at y
  have hcmp := hAB.dotProduct_mulVec_nonneg y
  have hstar' : star y = y := by
    funext i
    simp
  rw [hstar'] at hcmp
  have hcmp' : y ⬝ᵥ ((α • B - A) *ᵥ y) = α * (y ⬝ᵥ v) - y ⬝ᵥ (A *ᵥ y) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hBy]
  rw [hcmp'] at hcmp
  have hvy : v ⬝ᵥ y = y ⬝ᵥ v := dotProduct_comm _ _
  have hxv : x ⬝ᵥ v = v ⬝ᵥ x := dotProduct_comm _ _
  rw [hvy, hxv] at hpos
  have hαi : 0 < α⁻¹ := inv_pos.mpr hα
  have h1 : α⁻¹ * α = 1 := inv_mul_cancel₀ hα.ne'
  -- 0 ≤ v⬝x - 2α⁻¹ (y⬝v) + α⁻² q,  q ≤ α (y⬝v)
  have hq : α⁻¹ * α⁻¹ * (y ⬝ᵥ (A *ᵥ y)) ≤ α⁻¹ * (y ⬝ᵥ v) := by
    have h := mul_le_mul_of_nonneg_left (sub_nonneg.mp hcmp) (mul_nonneg hαi.le hαi.le)
    calc α⁻¹ * α⁻¹ * (y ⬝ᵥ (A *ᵥ y)) ≤ α⁻¹ * α⁻¹ * (α * (y ⬝ᵥ v)) := h
      _ = α⁻¹ * (α⁻¹ * α) * (y ⬝ᵥ v) := by ring
      _ = α⁻¹ * (y ⬝ᵥ v) := by rw [h1, mul_one]
  have h3 : α⁻¹ * (y ⬝ᵥ v) ≤ v ⬝ᵥ x := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hα.le
  rw [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul] at h4
  rw [hvy]
  exact h4
