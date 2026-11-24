-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaBasic.wFactor_neg_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:01.177744+00:00
-- url     : https://prove2.me/submissions/d4063aea-d490-4dae-97cd-fc62046abeab

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
theorem _root_.solution (l z : ℂ) : wFactor (-l) (-z) = wFactor l z := by
  simp only [wFactor, neg_div_neg_eq, neg_sq]
end Formalism.L2.Th1.F.SigmaBasic
