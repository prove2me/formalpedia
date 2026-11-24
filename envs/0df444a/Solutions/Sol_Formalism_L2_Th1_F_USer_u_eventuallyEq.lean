-- Prove2me | solution 1 for Formalism.L2.Th1.F.USer.u_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:18.904868+00:00
-- url     : https://prove2.me/submissions/b6e88ed4-cc82-4a2b-813b-0b6d04cf4d51

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_P_local
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_pExcept
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add


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
theorem _root_.solution (L : PeriodPair) :
    (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z)
      =ᶠ[nhds 0] fun z => z * num L z / den L z := by
  have hPl : L.weierstrassP = fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2 := funext fun w => by
    have := Formalism.L2.Th1.F.IsogenyPAux.P_local L 0 (zero_mem _) w
    simpa using this
  have hev := (TaylorSigmaUniqueness.analyticAt_pExcept L).eventually_analyticAt
  filter_upwards [hev] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp [hPl, PeriodPair.weierstrassPExcept_zero]
  · have hd : L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
      rw [← L.deriv_weierstrassP, hPl]
      have h1 : HasDerivAt (fun w => L.weierstrassPExcept 0 w) (deriv (L.weierstrassPExcept 0) z) z :=
        hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => 1 / w ^ 2) (-2 / z ^ 3) z := by
        have h3 := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
        have e : (fun w : ℂ => 1 / w ^ 2) = fun w => (w ^ 2)⁻¹ := funext fun w => one_div _
        rw [e]
        refine h3.congr_deriv ?_
        have e2 : (2 : ℕ) - 1 = 1 := rfl
        rw [e2]
        push_cast
        field_simp
      have h4 := (h1.add h2).deriv
      rw [show (fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2) =
        ((fun w => L.weierstrassPExcept 0 w) + fun w : ℂ => 1 / w ^ 2) from rfl, h4]
      ring
    rw [hd, hPl]
    simp only [num, den]
    by_cases hD : (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) = 0
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 = 0 := by
        have e : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 =
            (-2 / z ^ 3) * (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) := by
          field_simp
          ring
        rw [e, hD, mul_zero]
      rw [hD, hD', div_zero, div_zero]
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 ≠ 0 := by
        intro h
        apply hD
        have e : 1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z =
            (-(z ^ 3) / 2) * (deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3) := by
          field_simp
          ring
        rw [e, h, mul_zero]
      rw [div_eq_div_iff hD' hD]
      field_simp
      ring
end Formalism.L2.Th1.F.USer
