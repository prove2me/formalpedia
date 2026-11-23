-- Prove2me | solution 1 for Formalism.DivisionValues.det_le_det_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.918384+00:00
-- url     : https://prove2.me/submissions/a52d5cf6-b1ec-4ea5-ba03-73bb05bc2c2d

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Theorems.Thm_Formalism_DivisionValues_one_le_det_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : X.det ≤ (X + Y).det := by
  by_cases hXu : IsUnit X
  · have hX0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    have hSS : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX0
    have hS0 : (0 : Matrix m m ℂ) ≤ CFC.sqrt X := CFC.sqrt_nonneg X
    set S := CFC.sqrt X with hSdef
    have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
    have hSh : Sᴴ = S := hSpsd.1
    have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hXu)
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
    have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    have hTh : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
    have hZ : ((S⁻¹)ᴴ * Y * S⁻¹).PosSemidef := hY.conjTranspose_mul_mul_same _
    have hmid : S * (S⁻¹ * Y * S⁻¹) * S = Y := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h2, mul_one]
    have hsum : X + Y = S * (1 + (S⁻¹)ᴴ * Y * S⁻¹) * S := by
      rw [hTh, mul_add, add_mul, mul_one, hSS, hmid]
    have hdX : X.det = S.det * S.det := by rw [← hSS, det_mul]
    rw [hsum, det_mul, det_mul]
    have e : S.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det * S.det = X.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det := by
      rw [hdX]; ring
    rw [e]
    have hone := one_le_det_one_add hZ
    have hXd : 0 ≤ X.det := hX.det_nonneg
    have := mul_le_mul_of_nonneg_left hone hXd
    simpa using this
  · have hd : X.det = 0 := by
      by_contra h
      exact hXu ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h))
    rw [hd]
    exact (hX.add hY).det_nonneg
end Formalism.DivisionValues
