-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaBasic.differentiable_wFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:59.242018+00:00
-- url     : https://prove2.me/submissions/b2ae851a-3cc0-4fe0-8dd9-276410c4f3c8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaBasic
namespace Formalism.L2.Th1.F.SigmaBasic
theorem _root_.solution (l : ℂ) : Differentiable ℂ (wFactor l) := by
  unfold wFactor
  fun_prop
end Formalism.L2.Th1.F.SigmaBasic
