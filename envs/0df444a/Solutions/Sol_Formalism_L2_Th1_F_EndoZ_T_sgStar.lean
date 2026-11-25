-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.T_sgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:52.770005+00:00
-- url     : https://prove2.me/submissions/3cf216b3-8257-4eee-9072-0c09559acf1d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_P2M_Formalism_L2_Th1_F_EndoZ_taylorSgStar__73b480b36a76
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_sigmaEntire


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) :
    T (sgStar L) (Formalism.L2.Th1.C.sgStar (pSeries L) (s2 L)) := by
  refine ⟨?_, taylorSgStar' L⟩
  have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (-(s2 L) * z ^ 2 / 2) := by fun_prop
  have hd : Differentiable ℂ (sgStar L) := (sigmaEntire L).mul h1
  exact hd.analyticAt 0
end Formalism.L2.Th1.F.EndoZ
