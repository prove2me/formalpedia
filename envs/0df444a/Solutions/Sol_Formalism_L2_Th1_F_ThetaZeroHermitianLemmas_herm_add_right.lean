-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:01.391433+00:00
-- url     : https://prove2.me/submissions/29ea551d-fe93-4cd7-94f0-e669f16eb700

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
theorem _root_.solution (L : PeriodPair) (x y w : ℂ) : herm L w (x + y) = herm L w x + herm L w y := by
  simp only [herm, map_add]; ring
end Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
