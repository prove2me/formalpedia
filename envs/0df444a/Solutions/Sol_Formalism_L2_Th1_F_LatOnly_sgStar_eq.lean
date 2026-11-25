-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.sgStar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:49:14.752052+00:00
-- url     : https://prove2.me/submissions/b0de8b38-a921-4ef1-bf56-0b8c1f1c5ec1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wSigma_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_quasiPeriodConst_eq

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
theorem _root_.solution (h : L.lattice = L'.lattice) : sgStar L = sgStar L' := by
  funext z
  simp only [sgStar]
  rw [wSigma_eq h, quasiPeriodConst_eq h]
end Formalism.L2.Th1.F.LatOnly
