-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.wp_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:24.116437+00:00
-- url     : https://prove2.me/submissions/2d8d42ea-479e-42a9-9b77-13306af1e970

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_neg
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_unique
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_sgStarAdd
import Theorems.Thm_Formalism_L2_Th1_F_sigmaLogDeriv
import Theorems.Thm_Formalism_L2_Th1_F_sigmaZero

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
private theorem hasDerivAt_sgStar' (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) :
    HasDerivAt (sgStar L) (sgStar L u * (wZeta L u - s2 L * u)) u := by
  have h1 := sigmaLogDeriv L u hu
  have h3 : HasDerivAt (fun w : ℂ => -(s2 L) * w ^ 2 / 2) (-(s2 L) * u) u :=
    (((hasDerivAt_pow 2 u).const_mul (-(s2 L))).div_const 2).congr_deriv (by norm_num <;> ring)
  have h5 := h1.mul h3.cexp
  unfold sgStar
  exact h5.congr_deriv (by ring)
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
theorem _root_.solution (L : PeriodPair) {P z : ℂ} (hP : P ∉ L.lattice) (hz : z ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    L.derivWeierstrassP z = (L.weierstrassP z - L.weierstrassP P)
      * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z) := by
  have hz' : ∀ᶠ u in 𝓝 z, u ∉ L.lattice :=
    (PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hz
  have hev : (fun u => sgStar L (u + P) * sgStar L (u - P)) =ᶠ[𝓝 z]
      fun u => -(sgStar L u ^ 2 * sgStar L P ^ 2 * (L.weierstrassP u - L.weierstrassP P)) := by
    filter_upwards [hz'] with u hu
    exact sgStarAdd L u P hu hP
  have hg := ((hasDerivAt_sgStar' L hp).comp z ((hasDerivAt_id' z).add_const P)).mul
    ((hasDerivAt_sgStar' L hm).comp z ((hasDerivAt_id' z).sub_const P))
  have hsq : HasDerivAt (fun u => sgStar L u ^ 2)
      (2 * sgStar L z * (sgStar L z * (wZeta L z - s2 L * z))) z := by
    exact ((hasDerivAt_sgStar' L hz).pow 2).congr_deriv (by norm_num <;> ring)
  have hh := ((hsq.mul_const (sgStar L P ^ 2)).mul
    ((PDeriv.hasDerivAt_P L hz).sub_const (L.weierstrassP P))).neg
  have heq := hg.unique (hh.congr_of_eventuallyEq hev)
  simp only [Function.comp_apply] at heq
  have hAB := sgStarAdd L z P hz hP
  have hs : sgStar L z ≠ 0 := mul_ne_zero (fun h => hz ((sigmaZero L z).1 h)) (Complex.exp_ne_zero _)
  have hc : sgStar L P ≠ 0 := mul_ne_zero (fun h => hP ((sigmaZero L P).1 h)) (Complex.exp_ne_zero _)
  have key : sgStar L z ^ 2 * sgStar L P ^ 2 * (L.derivWeierstrassP z - (L.weierstrassP z
      - L.weierstrassP P) * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z)) = 0 := by
    linear_combination heq - (wZeta L (z + P) + wZeta L (z - P) - 2 * s2 L * z) * hAB
  have h0 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hc))
  linear_combination h0
end Formalism.L2.Th1.F.EndoZ
