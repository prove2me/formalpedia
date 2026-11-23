-- Prove2me | solution 1 for Formalism.DivisionValues.inv_real_smul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:18.238629+00:00
-- url     : https://prove2.me/submissions/dfdbb2f8-94a3-4ac2-8bfc-91e656cbaccb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

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
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s : ℝ) : ℂ) • A)⁻¹ = ((s⁻¹ : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s⁻¹ : ℝ) : ℂ) * ((s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]
end Formalism.DivisionValues
