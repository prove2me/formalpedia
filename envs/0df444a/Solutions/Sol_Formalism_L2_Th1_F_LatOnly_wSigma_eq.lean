-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.wSigma_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:42.551707+00:00
-- url     : https://prove2.me/submissions/4ef75872-51d6-47d3-91ff-bad42de03786

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_tprod_submodule_congr

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
open Formalism.L2.Th1.F.LatOnly
variable {L L' : PeriodPair}
namespace Formalism.L2.Th1.F.LatOnly
theorem _root_.solution (h : L.lattice = L'.lattice) : wSigma L = wSigma L' := by
  funext z
  simp only [wSigma]
  rw [tprod_submodule_congr h (fun w => wFactor w z)]
end Formalism.L2.Th1.F.LatOnly
