-- Prove2me | solution 1 for Formalism.L2.Th1.F.isogeny_formula_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:46.521385+00:00
-- url     : https://prove2.me/submissions/14a2ca15-ee84-4a8b-b3f8-7e18b7e13647

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_prod
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_unique
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ev_notMem
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_fP
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sgStar
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_fP_eq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_prod_const
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
import Theorems.Thm_Formalism_L2_Th1_F_isogenySigma
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
open EndoZ TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution : IsogenyFormulaInstance := by
  intro L α S hα hm hS
  have hX : T (fun z : ℂ => z) PowerSeries.X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have hsg := T_sgStar L
  have hL := T.mul taylor_ring (T.pow taylor_ring (T.rescale α hsg) 2)
    (T.pow taylor_ring hX (2 * Fintype.card S))
  have hR := T.mul taylor_ring
    (T.mul taylor_ring (T_const (α ^ 2))
      (T.pow taylor_ring hsg (2 * (Fintype.card S + 1))))
    (T.prod Finset.univ (fun (P : S) (z : ℂ) => fP L P z)
      (fun (P : S) => Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP (P : ℂ)))
      (fun P _ => T_fP L P))
  have heq := T.unique hL hR (by
    filter_upwards [ev_notMem L, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    beta_reduce
    have hsig := isogenySigma L α S hα hm hS z hz
    have hp : ∏ P : S, fP L (P : ℂ) z
        = ∏ P : S, (z ^ 2 * (L.weierstrassP z - L.weierstrassP (P : ℂ))) :=
      Finset.prod_congr rfl fun P _ => fP_eq L P hz0'
    rw [hp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_coe_sort S (fun P => L.weierstrassP z - L.weierstrassP P), hsig,
      Fintype.card_coe]
    ring)
  unfold Formalism.L2.Th1.C.IsogenyFormula
  exact heq
end Formalism.L2.Th1.F
