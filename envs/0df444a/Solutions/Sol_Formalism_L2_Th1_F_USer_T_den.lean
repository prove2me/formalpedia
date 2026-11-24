-- Prove2me | solution 1 for Formalism.L2.Th1.F.USer.T_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:57.560305+00:00
-- url     : https://prove2.me/submissions/a9b54073-f6e6-4e70-a251-7108a96bb7a8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_pExcept
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
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
theorem _root_.solution (hr : TaylorRing) (hd : TaylorDeriv) (L : PeriodPair) :
    T (den L) (1 - C (1 / 2 : ℂ) * X ^ 3 * derivative ℂ (pSeries L)) := by
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hP := TaylorSigmaUniqueness.analyticAt_pExcept L
  have hPd : AnalyticAt ℂ (deriv (L.weierstrassPExcept 0)) 0 := hP.deriv
  have hz : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hz2 : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hz.mul hz
  have hz3 : AnalyticAt ℂ (fun z : ℂ => z * z * z) 0 := hz2.mul hz
  have hc3 : AnalyticAt ℂ (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) 0 := analyticAt_const.mul hz3
  have hprod : AnalyticAt ℂ (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) 0 :=
    hc3.mul hPd
  have e : den L = fun z => (fun _ : ℂ => (1 : ℂ)) z +
      (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) z := by
    funext z
    simp only [den]
    ring
  refine ⟨by rw [e]; exact analyticAt_const.add hprod, ?_⟩
  have h1 : taylor0 (den L) = taylor0 (fun _ : ℂ => (1 : ℂ)) +
      taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) := by
    rw [e]
    exact (hadd _ _ analyticAt_const hprod).1
  have h2 : taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) =
      taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) * taylor0 (deriv (L.weierstrassPExcept 0)) :=
    (hadd (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) (deriv (L.weierstrassPExcept 0)) hc3 hPd).2
  have h3 : taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) =
      taylor0 (fun _ : ℂ => -(1 / 2 : ℂ)) * taylor0 (fun z : ℂ => z * z * z) :=
    (hadd (fun _ : ℂ => -(1 / 2 : ℂ)) (fun z : ℂ => z * z * z) analyticAt_const hz3).2
  have h4 : taylor0 (fun z : ℂ => z * z * z) = taylor0 (fun z : ℂ => z * z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z * z) (fun z : ℂ => z) hz2 hz).2
  have h5 : taylor0 (fun z : ℂ => z * z) = taylor0 (fun z : ℂ => z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z) (fun z : ℂ => z) hz hz).2
  rw [h1, h2, h3, h4, h5, hC, hC, hX, hd.1 _ hP, map_one, map_neg]
  show _ = 1 - PowerSeries.C (1 / 2 : ℂ) * PowerSeries.X ^ 3 * PowerSeries.derivative ℂ (taylor0 (L.weierstrassPExcept 0))
  ring
end Formalism.L2.Th1.F.USer
