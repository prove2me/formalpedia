-- Prove2me | solution 1 for Formalism.L2.Th1.F.uSerLattice_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:44:26.052944+00:00
-- url     : https://prove2.me/submissions/cdec3800-e1d5-41f0-8f15-108a28cb05c5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen
import Theorems.Thm_Formalism_L2_Th1_F_USer_uSerLattice_gen
import Theorems.Thm_Formalism_L2_Th1_F_taylor_deriv
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring


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
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution (hp : POfLattice) (hn : WpNumDen) : USerLattice := USer.uSerLattice_gen taylor_ring taylor_deriv hp hn
end Formalism.L2.Th1.F
