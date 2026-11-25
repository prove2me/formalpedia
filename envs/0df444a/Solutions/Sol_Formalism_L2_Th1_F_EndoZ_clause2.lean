-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.clause2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:02.677896+00:00
-- url     : https://prove2.me/submissions/7d0394c3-f455-40c0-a86d-093139865d7f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sub
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_unique
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_p
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_shift
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_wp_congr
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_U_mem
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_d2log_fP
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_fP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_wp_congr
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
theorem _root_.solution (L : PeriodPair) {P Q : ℂ} (hP : P ∉ L.lattice) (hQ : Q + P ∈ L.lattice) :
    Formalism.L2.Th1.C.HasSecondLogDeriv (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP P))
      (2 * pSeries L - taylor0 (fun z => L.weierstrassP (z + P))
        - taylor0 (fun z => L.weierstrassP (z + Q))) := by
  have hF := T_fP L P
  have h1 := T.deriv hF
  have h2 := T.deriv h1
  have hL := T.sub (T.mul taylor_ring h2 hF) (T.pow taylor_ring h1 2)
  have hQn : Q ∉ L.lattice := by
    intro hq; apply hP
    have h3 := L.lattice.sub_mem hQ hq
    rwa [add_sub_cancel_left] at h3
  have hR := T.mul taylor_ring
    (T.sub (T.sub (T.mul taylor_ring (T_const 2) (T_p L)) (T_shift L hP)) (T_shift L hQn))
    (T.pow taylor_ring hF 2)
  have heq := T.unique hL hR (by
    filter_upwards [U_mem L hP] with w hw
    have hc : L.weierstrassP (w + Q) = L.weierstrassP (w - P) := wp_congr L (by
      have e : w + Q - (w - P) = Q + P := by ring
      rw [e]; exact hQ)
    beta_reduce
    rw [d2log_fP L hP hw, hc])
  unfold Formalism.L2.Th1.C.HasSecondLogDeriv
  rw [heq, show (C (2 : ℂ) : PowerSeries ℂ) = 2 from map_ofNat C 2]
end Formalism.L2.Th1.F.EndoZ
