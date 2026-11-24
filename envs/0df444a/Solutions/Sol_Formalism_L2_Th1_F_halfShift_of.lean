-- Prove2me | solution 1 for Formalism.L2.Th1.F.halfShift_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:41.339609+00:00
-- url     : https://prove2.me/submissions/19128da0-2a4e-4da8-acf5-0c505eaa87b6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_derivP_half
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_prod_const
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_notMem_of_comb

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
theorem _root_.solution (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (hi : PInjective) :
    HalfShift := by
  intro L t z ht h2 hzL hzt
  have hσt : wSigma L t ≠ 0 := mt (hz L t).1 ht
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Complex.exp (wEta L (2 * t) * t) / wSigma L t ^ 4 := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]; exact div_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ hσt)
  have hconst : ∀ w, w ∉ L.lattice → w + t ∉ L.lattice →
      (L.weierstrassP (w + t) - L.weierstrassP t) * (L.weierstrassP w - L.weierstrassP t) = κ := by
    intro w hw hwt
    rw [hκdef, eq_div_iff (pow_ne_zero _ hσt)]
    exact prod_const ha hq hz L ht h2 hw hwt
  suffices hκ : κ = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4 by rw [hconst z hzL hzt, hκ]
  have n1 : t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 4 0 (by push_cast; ring)
  have n2 : t / 4 + t ∉ L.lattice := notMem_of_comb L ht h2 _ 4 (-2) (by push_cast; ring)
  have n3 : t / 4 + t + t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 2 (-1) (by push_cast; ring)
  have hne : L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4) ≠ 0 := by
    intro h
    rcases (hi L _ _ n2 n1).1 (sub_eq_zero.mp h) with h | h
    · exact ht (by simpa using h)
    · exact n3 h
  have hev : ∀ᶠ w in 𝓝 (t / 4), (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t) = κ := by
    have c1 : ∀ᶠ w in 𝓝 (t / 4), w ∉ L.lattice := (isOpen_compl L).mem_nhds n1
    have c2 : ∀ᶠ w in 𝓝 (t / 4), w + t ∉ L.lattice :=
      ((continuous_id.add continuous_const).tendsto (t / 4)).eventually ((isOpen_compl L).mem_nhds n2)
    filter_upwards [c1, c2] with w h1 h2 using hconst w h1 h2
  have hder : HasDerivAt (fun w => (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t))
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) (t / 4) :=
    (((hasDerivAt_P L n2).comp_add_const (t / 4) t).sub_const _).mul
      ((hasDerivAt_P L n1).sub_const _)
  have d := hder.unique ((hasDerivAt_const (t / 4) κ).congr_of_eventuallyEq hev)
  have s1 := L.derivWeierstrassP_sq _ n2
  have s2 := L.derivWeierstrassP_sq _ n1
  have s0 := L.derivWeierstrassP_sq _ ht
  rw [derivP_half L h2] at s0
  have k := hconst _ n1 n2
  have key : κ * (L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4))
      * (4 * κ - (12 * L.weierstrassP t ^ 2 - L.g₂)) = 0 := by
    rw [← k]
    linear_combination
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) * d
      - (L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2 * s1
      + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2 * s2
      + ((L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2) * s0
  have h4 := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hκ0 hne)
  linear_combination (1 / 4 : ℂ) * h4
end Formalism.L2.Th1.F
