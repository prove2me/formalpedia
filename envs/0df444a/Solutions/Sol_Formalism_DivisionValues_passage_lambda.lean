-- Prove2me | solution 1 for Formalism.DivisionValues.passage_lambda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:19.071501+00:00
-- url     : https://prove2.me/submissions/b118ea70-c634-41c7-b4f8-306f23095407

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
theorem _root_.solution : PassageLam := by
  intro lam0 f r g Cg L b hf h1 h2
  have hfr : 0 ≤ f * r ^ 2 := mul_nonneg hf (sq_nonneg r)
  have h3 : f * r ^ 2 * Real.log g ≤ f * r ^ 2 * (Cg * L) := mul_le_mul_of_nonneg_left h2 hfr
  exact ⟨by linarith, by linarith, fun hb => by linarith⟩
end Formalism.DivisionValues
