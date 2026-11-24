-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.clause3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:24.17473+00:00
-- url     : https://prove2.me/submissions/f28eb72e-3ce2-4e25-b615-2b5cbc22f4e0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sub
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sum
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_unique
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_p
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_shift
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ev_notMem
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_tendsto_mul_nhdsNE
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_isogenyP
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
theorem _root_.solution (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) :
    C (α ^ 2) * rescale α (pSeries L) = pSeries L
      + ∑ P : S, (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - C (L.weierstrassP (P : ℂ))) := by
  have hL := T.mul taylor_ring (T_const (α ^ 2)) (T.rescale α (T_p L))
  have hR := T.add taylor_ring (T_p L) (T.sum Finset.univ
    (fun (P : S) (z : ℂ) => L.weierstrassP (z + (P : ℂ)) - L.weierstrassP (P : ℂ))
    (fun (P : S) => taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - C (L.weierstrassP (P : ℂ)))
    (fun P _ => T.sub (T_shift L (hS.1 P P.2).2) (T_const _)))
  refine T.unique hL hR ?_
  filter_upwards [ev_notMem L, (tendsto_mul_nhdsNE hα).eventually (ev_notMem L),
    self_mem_nhdsWithin] with z hz hαz hz0
  have hz0' : z ≠ 0 := hz0
  have hip := isogenyP L α S hα hm hS z hαz
  rw [← Finset.sum_coe_sort S] at hip
  have e1 : L.weierstrassPExcept 0 (α * z) = L.weierstrassP (α * z) - 1 / (α * z) ^ 2 := by
    rw [wp_eq L (α * z)]; ring
  have e2 : L.weierstrassPExcept 0 z = L.weierstrassP z - 1 / z ^ 2 := by
    rw [wp_eq L z]; ring
  beta_reduce
  rw [e1, e2, mul_sub, hip]
  field_simp
  ring
end Formalism.L2.Th1.F.EndoZ
