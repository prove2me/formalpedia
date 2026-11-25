-- Prove2me | solution 1 for Formalism.DivisionValues.passage_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:24.028179+00:00
-- url     : https://prove2.me/submissions/92b44dfc-8f4f-48f0-9926-5fe492fb6a3f

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
namespace Formalism.DivisionValues
theorem _root_.solution : PassageQ := by
  intro mu0 HH0 lam0 logκ c2 cq f r g k b p1 p2 hc2 hk hb hg hlam hmu hHH
  have hb0 : 0 ≤ b := by linarith
  have hcl : c2 * lam0 ≤ c2 * b := mul_le_mul_of_nonneg_left hlam hc2
  refine ⟨by linarith, fun hP => by nlinarith [mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hb)],
    fun h => ?_⟩
  have hkb0 : 0 ≤ k * b := by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]
  have h1 : cq * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 7 * b := mul_le_mul_of_nonneg_right h hb0
  have h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)
  have h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8 := by ring
  calc cq * f * r * ((p1 + p2 + c2) * b) = cq * f * r * (p1 + p2 + c2) * b := by ring
    _ ≤ g := by linarith
end Formalism.DivisionValues
