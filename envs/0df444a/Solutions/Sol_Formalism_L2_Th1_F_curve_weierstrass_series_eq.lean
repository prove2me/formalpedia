-- Prove2me | solution 1 for Formalism.L2.Th1.F.curve_weierstrass_series_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:46.065456+00:00
-- url     : https://prove2.me/submissions/c412cefe-0456-4cf1-a91f-d5b606b89dc4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Theorems.Thm_Formalism_L2_Th1_F_curveBridge_of
import Theorems.Thm_Formalism_L2_Th1_A_bridgeWp
import Theorems.Thm_Formalism_L2_Th1_F_taylorIsWp_of
import Theorems.Thm_Formalism_L2_Th1_F_taylor_deriv
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring
import Theorems.Thm_Formalism_L2_Th1_F_weierstrass_series_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : CurveBridge :=
  curveBridge_of Formalism.L2.Th1.A.bridgeWp weierstrass_series_unique (taylorIsWp_of taylor_ring taylor_deriv)
end Formalism.L2.Th1.F
