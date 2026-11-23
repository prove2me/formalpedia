-- Prove2me | solution 1 for Formalism.DivisionValues.gram_matrix_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:30.212056+00:00
-- url     : https://prove2.me/submissions/358a2430-694f-4e6f-b645-6c5ddd6fefdf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_gramR_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open ValuationRepresentative
namespace Formalism.DivisionValues
theorem _root_.solution : GramChange := by
  intro K _ _ D m Γ e γ
  have h : Matrix.of (fun i => ∑ k, γ k i • e k) = γᵀ * Matrix.of e := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hm : (γᵀ * Matrix.of e).map star = γᵀ.map star * (Matrix.of e).map star := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      star_sum, star_mul']
  have hd : (γᵀ.map star).det = star γ.det := Matrix.det_conjTranspose γ
  have hr : γᵀ.map star * (Matrix.of e).map star * Γ * ((Matrix.of e)ᵀ * γ) =
      γᵀ.map star * ((Matrix.of e).map star * Γ * (Matrix.of e)ᵀ) * γ := by
    simp only [Matrix.mul_assoc]
  rw [gramR_eq, gramR_eq, h, hm, Matrix.transpose_mul, Matrix.transpose_transpose, hr,
    Matrix.det_mul, Matrix.det_mul, hd]
  ring
end Formalism.DivisionValues
