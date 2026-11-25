-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_half_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:20.975317+00:00
-- url     : https://prove2.me/submissions/dff3ed30-a944-42ec-9f09-e43b748765cd

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
theorem _root_.solution (L : PeriodPair) (x w : ℂ) : herm L x (w / 2) = herm L x w / 2 := by
  simp only [herm, map_div₀, map_ofNat]; ring
end Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
