-- Prove2me | solution 1 for D1Bound5.productFive_inverse_vector_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:38.385919+00:00
-- url     : https://prove2.me/submissions/65db7261-e6b7-4c81-abee-45d402e161d9

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveInverseVector_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero
import Theorems.Thm_D1Bound5_reference_perturbed_inverse_norm_lt

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5




private theorem fiveY_reference :
    halfOffDiagonal *ᵥ fiveY = fiveZ := by
  ext i
  fin_cases i <;>
    simp (config := {decide := true}) [halfOffDiagonal, fiveY, fiveZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

private theorem fiveY_norm :
    ‖(WithLp.toLp 2 fiveY : EuclideanSpace ℂ (Fin 4))‖ = (2/3 : ℝ) := by
  let y : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 fiveY
  have hsq : ‖y‖^2 = (2/3 : ℝ)^2 := by
    rw [EuclideanSpace.norm_sq_eq y, Fin.sum_univ_four]
    norm_num [y, fiveY]
  have hn := norm_nonneg y
  dsimp [y] at *
  nlinarith only [hsq, hn]


/-- An L2 inverse-vector bound that exploits the constant reference eigenvector.
The coordinatewise last-column estimate is deliberately an explicit input. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ)
    (hnear : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ))
    (hv : ‖(WithLp.toLp 2 (fun i => v i - (1/2 : ℂ)) :
        EuclideanSpace ℂ (Fin 4))‖ < (1/200 : ℝ)) :
    ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin 4))‖ <
      (11/12 : ℝ) := by
  let y : Fin 4 → ℂ := fiveY
  let z : Fin 4 → ℂ := fiveZ
  have hy : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin 4))‖ =
      (2/3 : ℝ) := fiveY_norm
  have hHz : halfOffDiagonal *ᵥ y = z := fiveY_reference
  have hv' : ‖(WithLp.toLp 2 (v - z) : EuclideanSpace ℂ (Fin 4))‖ <
      (1/200 : ℝ) := by
    have hh : v - z = fun i => v i - (1/2 : ℂ) := by
      ext i
      simp [z, fiveZ, Pi.sub_apply]
    simpa only [hh] using hv
  have hsmall : ‖F - halfOffDiagonal‖ < (1/8 : ℝ) :=
    lt_of_le_of_lt hnear (by norm_num)
  have hInv : ‖F⁻¹‖ < (8/3 : ℝ) :=
    reference_perturbed_inverse_norm_lt F hsmall
  have hQ : ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1 := by
    calc
      _ ≤ ‖halfOffDiagonalInverse‖ * ‖F - halfOffDiagonal‖ :=
        Matrix.l2_opNorm_mul _ _
      _ = 2 * ‖F - halfOffDiagonal‖ := by
        rw [halfOffDiagonalInverse_norm]
      _ ≤ 2 * (11/96 : ℝ) :=
        mul_le_mul_of_nonneg_left hnear (by norm_num)
      _ < 1 := by norm_num
  have hdet : F.det ≠ 0 := reference_perturbed_det_ne_zero F hQ
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
  have hleft : F⁻¹ *ᵥ (F *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul F hu,
      Matrix.one_mulVec]
  have hFdecomp : (F - halfOffDiagonal) + halfOffDiagonal = F :=
    sub_add_cancel F halfOffDiagonal
  have hresid : v - F *ᵥ y =
      (v - z) - (F - halfOffDiagonal) *ᵥ y := by
    calc
      v - F *ᵥ y = v - ((F - halfOffDiagonal) + halfOffDiagonal) *ᵥ y := by
        rw [hFdecomp]
      _ = (v - z) - (F - halfOffDiagonal) *ᵥ y := by
        rw [Matrix.add_mulVec, hHz]
        abel
  have hresnorm : ‖(WithLp.toLp 2 (v - F *ᵥ y) :
      EuclideanSpace ℂ (Fin 4))‖ <
      (1/200 : ℝ) + (11/96 : ℝ) * (2/3 : ℝ) := by
    rw [hresid]
    calc
      _ ≤ ‖(WithLp.toLp 2 (v - z) : EuclideanSpace ℂ (Fin 4))‖ +
          ‖(WithLp.toLp 2 ((F - halfOffDiagonal) *ᵥ y) :
            EuclideanSpace ℂ (Fin 4))‖ :=
        norm_sub_le _ _
      _ ≤ ‖(WithLp.toLp 2 (v - z) : EuclideanSpace ℂ (Fin 4))‖ +
          ‖F - halfOffDiagonal‖ *
            ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin 4))‖ := by
        have hcast :
            (EuclideanSpace.equiv (Fin 4) ℂ).symm ((F - halfOffDiagonal) *ᵥ y) =
            (WithLp.toLp 2 ((F - halfOffDiagonal) *ᵥ y) :
              EuclideanSpace ℂ (Fin 4)) := by
          ext i
          rfl
        have hh := Matrix.l2_opNorm_mulVec (F - halfOffDiagonal)
          (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin 4))
        rw [hcast] at hh
        linarith only [hh]
      _ < (1/200 : ℝ) + (11/96 : ℝ) * (2/3 : ℝ) := by
        rw [hy]
        have hprod := mul_le_mul_of_nonneg_right hnear (by norm_num : (0:ℝ) ≤ 2/3)
        linarith only [hv', hprod]
  have hdiff : F⁻¹ *ᵥ v - y =
      F⁻¹ *ᵥ (v - F *ᵥ y) := by
    rw [Matrix.mulVec_sub, hleft]
  have hdiffnorm : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v - y) :
      EuclideanSpace ℂ (Fin 4))‖ <
      (8/3 : ℝ) * ((1/200 : ℝ) + (11/96 : ℝ) * (2/3 : ℝ)) := by
    rw [hdiff]
    calc
      _ ≤ ‖F⁻¹‖ * ‖(WithLp.toLp 2 (v - F *ᵥ y) :
          EuclideanSpace ℂ (Fin 4))‖ :=
        Matrix.l2_opNorm_mulVec F⁻¹
          (WithLp.toLp 2 (v - F *ᵥ y) : EuclideanSpace ℂ (Fin 4))
      _ ≤ (8/3 : ℝ) * ‖(WithLp.toLp 2 (v - F *ᵥ y) :
          EuclideanSpace ℂ (Fin 4))‖ :=
        mul_le_mul_of_nonneg_right hInv.le (norm_nonneg _)
      _ < _ := mul_lt_mul_of_pos_left hresnorm (by norm_num)
  let x : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (F⁻¹ *ᵥ v)
  let e : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (F⁻¹ *ᵥ v - y)
  let b : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 y
  have hx : x = e + b := by
    ext i
    change (F⁻¹ *ᵥ v) i = ((F⁻¹ *ᵥ v) i - y i) + y i
    ring
  have htri : ‖x‖ ≤ ‖e‖ + ‖b‖ := by
    rw [hx]
    exact norm_add_le e b
  change ‖x‖ < (11/12 : ℝ)
  linarith only [htri, hdiffnorm, hy]

end D1Bound5
end
