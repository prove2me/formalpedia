-- Prove2me | solution 1 for Formalism.DivisionValues.passage_scale_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:58.517822+00:00
-- url     : https://prove2.me/submissions/4e0c0950-7c10-4a9a-b57a-baa70214ab0a

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
theorem _root_.solution : PassageScaleFree := by
  intro muC mu0 HH0 lam0 de c1 c2 c3 τ0 τs
  have e : (mu0 + τ0) + (HH0 - τ0) + c2 * lam0 = mu0 + HH0 + c2 * lam0 := by ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor <;> intro h <;> linarith
end Formalism.DivisionValues
