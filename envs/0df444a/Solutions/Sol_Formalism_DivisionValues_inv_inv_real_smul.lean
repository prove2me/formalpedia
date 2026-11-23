-- Prove2me | solution 1 for Formalism.DivisionValues.inv_inv_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:40.777893+00:00
-- url     : https://prove2.me/submissions/dff873b1-f4fd-487e-986b-b94a1b54588c

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
    (((s⁻¹ : ℝ) : ℂ) • A)⁻¹ = ((s : ℝ) : ℂ) • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA, smul_smul]
  have h : ((s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one]
  rw [h, one_smul]
end Formalism.DivisionValues
