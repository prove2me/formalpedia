-- Prove2me | solution 1 for Formalism.L2.Th1.F.weierstrass_p_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:10.248859+00:00
-- url     : https://prove2.me/submissions/bab04ef0-32dd-4d5f-b2f9-667f46e3a968

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_derivWeierstrassP_not_eventually_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open HalfPeriodDerivative
namespace Formalism.L2.Th1.F
theorem _root_.solution : PSecond := by
  intro L z hz
  have hA := L.analyticOnNhd_derivWeierstrassP z hz
  have hd := hA.differentiableAt.hasDerivAt
  set D : ℂ → ℂ := fun w => deriv L.derivWeierstrassP w - (6 * L.weierstrassP w ^ 2 - L.g₂ / 2) with hD
  have hDan : AnalyticAt ℂ D z := by
    have h1 := hA.deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub (((analyticAt_const).mul (h2.pow 2)).sub analyticAt_const)
  have hmem : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := (isOpen_compl L).mem_nhds hz
  have hmul : ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w * D w = 0 := by
    have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ v in 𝓝 w, v ∉ L.lattice := hmem.eventually_nhds
    filter_upwards [hev] with w hw
    have hwL : w ∉ L.lattice := hw.self_of_nhds
    have e1 : HasDerivAt (fun v => L.derivWeierstrassP v ^ 2)
        (2 * L.derivWeierstrassP w * deriv L.derivWeierstrassP w) w := by
      simpa using ((L.analyticOnNhd_derivWeierstrassP w hwL).differentiableAt.hasDerivAt).fun_pow 2
    have e2 : HasDerivAt (fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃)
        (4 * (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w) - L.g₂ * L.derivWeierstrassP w) w := by
      simpa using ((((hasDerivAt_P L hwL).fun_pow 3).const_mul 4).sub
        ((hasDerivAt_P L hwL).const_mul L.g₂)).sub_const L.g₃
    have e3 : (fun v => L.derivWeierstrassP v ^ 2) =ᶠ[𝓝 w]
        fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃ := by
      filter_upwards [hw] with v hv using L.derivWeierstrassP_sq v hv
    have e4 := (e2.congr_of_eventuallyEq e3).unique e1
    simp only [hD]
    linear_combination (-1 / 2 : ℂ) * e4
  have hD0 : D z = 0 := by
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (derivWeierstrassP_not_eventually_zero L hz)
    · have h5 : ∀ᶠ w in 𝓝[≠] z, D w = 0 := by
        filter_upwards [h, hmul.filter_mono nhdsWithin_le_nhds] with w h1 h2
        exact (mul_eq_zero.mp h2).resolve_left h1
      have h6 : Tendsto D (𝓝[≠] z) (𝓝 (D z)) := hDan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h7 : Tendsto D (𝓝[≠] z) (𝓝 0) := tendsto_const_nhds.congr' (h5.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique h6 h7
  have : deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
    simpa [hD, sub_eq_zero] using hD0
  rwa [this] at hd
end Formalism.L2.Th1.F
