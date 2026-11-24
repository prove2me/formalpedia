-- Prove2me | solution 1 for Formalism.L2.Th1.F.USer.uSerLattice_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:52:02.470141+00:00
-- url     : https://prove2.me/submissions/0b9545a7-391f-4702-8267-cd0ed8abbc40

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen
import Theorems.Thm_Formalism_L2_Th1_F_USer_T_num
import Theorems.Thm_Formalism_L2_Th1_F_USer_T_den
import Theorems.Thm_Formalism_L2_Th1_F_USer_den_zero
import Theorems.Thm_Formalism_L2_Th1_F_USer_u_eventuallyEq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul


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
open Formalism.L2.Th1.F.USer
namespace Formalism.L2.Th1.F.USer
theorem _root_.solution (hr : TaylorRing) (hd : TaylorDeriv) (hp : POfLattice) (hn : WpNumDen) :
    USerLattice := by
  intro L
  have hN := T_num hr L
  have hD := T_den hr hd L
  have hden0 : den L 0 = 1 := den_zero L
  have hev := u_eventuallyEq L
  have hne : den L 0 ≠ 0 := by rw [hden0]; exact one_ne_zero
  have hzN : AnalyticAt ℂ (fun z => z * num L z) 0 := analyticAt_id.mul hN.1
  have hinv : AnalyticAt ℂ (fun z => (den L z)⁻¹) 0 := hD.1.inv hne
  have hquot : AnalyticAt ℂ (fun z => z * num L z / den L z) 0 := hzN.div hD.1 hne
  refine ⟨hquot.congr hev.symm, ?_⟩
  have h0 : taylor0 (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z) =
      taylor0 (fun z => z * num L z / den L z) := hr.2.2.2 _ _ hev
  have h1 : taylor0 (fun z => z * num L z / den L z) =
      taylor0 (fun z => z * num L z) * taylor0 (fun z => (den L z)⁻¹) := by
    have e : (fun z => z * num L z / den L z) = fun z => (z * num L z) * (den L z)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [e]
    exact (hr.1 (fun z => z * num L z) (fun z => (den L z)⁻¹) hzN hinv).2
  have h2 : taylor0 (fun z => z * num L z) = taylor0 (fun z : ℂ => z) * taylor0 (num L) :=
    (hr.1 (fun z : ℂ => z) (num L) analyticAt_id hN.1).2
  have hmul : taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) = 1 := by
    have e1 : taylor0 (fun z => (den L z)⁻¹ * den L z) =
        taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) :=
      (hr.1 (fun z => (den L z)⁻¹) (den L) hinv hD.1).2
    have hc := hD.1.continuousAt.eventually_ne hne
    have e2 : taylor0 (fun z => (den L z)⁻¹ * den L z) = taylor0 (fun _ : ℂ => (1 : ℂ)) := by
      refine hr.2.2.2 _ _ ?_
      filter_upwards [hc] with z hz
      exact inv_mul_cancel₀ hz
    rw [← e1, e2, hr.2.1, map_one]
  have hc0 : PowerSeries.constantCoeff (taylor0 (den L)) ≠ 0 := by
    rw [hD.2]
    simp
  have hinv2 : taylor0 (fun z => (den L z)⁻¹) = (taylor0 (den L))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hc0).mpr hmul
  rw [h0, h1, h2, hinv2, hr.2.2.1, hN.2, hD.2]
  unfold uSer
  rw [(hn ℂ L.g₂ L.g₃).1, (hn ℂ L.g₂ L.g₃).2, ← hp L]
end Formalism.L2.Th1.F.USer
