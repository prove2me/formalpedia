-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.T.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:05.767424+00:00
-- url     : https://prove2.me/submissions/f5f14a8d-57cf-406a-a697-93d01aa69777

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Formalism.L2.Th1.F
namespace EndoZ
open PowerSeries TaylorWp
private theorem T_const (c : ℂ) : T (fun _ => c) (C c) :=
  ⟨analyticAt_const, taylor_ring.2.1 c⟩
end EndoZ
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
namespace T
theorem _root_.solution {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) : T (fun z => -f z) (-F) := by
  convert T.mul taylor_ring (T_const (-1)) hf using 1
  · funext z; simp
  · simp
end T
end Formalism.L2.Th1.F.EndoZ
