-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.T_fP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:29.510031+00:00
-- url     : https://prove2.me/submissions/ffccb0ab-6dff-434d-addd-bf42e9dfc129

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sub
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_p
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
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
theorem _root_.solution (L : PeriodPair) (P : ℂ) :
    T (fP L P) (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP P)) := by
  have hX : T (fun z : ℂ => z) X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have h := T.add taylor_ring (T_const 1) (T.mul taylor_ring
    (T.pow taylor_ring hX 2) (T.sub (T_p L) (T_const (L.weierstrassP P))))
  unfold fP Formalism.L2.Th1.C.wpShift
  convert h using 1
  simp
end Formalism.L2.Th1.F.EndoZ
