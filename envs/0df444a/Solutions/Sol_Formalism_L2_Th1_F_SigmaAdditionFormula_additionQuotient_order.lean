-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:58.005105+00:00
-- url     : https://prove2.me/submissions/d885d39e-610d-4e79-adb1-9c308a77f47a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_periodic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_analyticAt_dslope
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_sigma_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionNumerator_neg
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_analyticAt_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_mul_eventuallyEq
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_analyticAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
private lemma exists_twistedGamma_eq_sq_mul_analytic (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ m : ℂ → ℂ, AnalyticAt ℂ m 0 ∧ ∀ y, frobeniusStickelbergerDetMulSigmaCube L w y = y ^ 2 * m y := by
  have hg0 := twistedGamma_zero L w ho hz hs

  have hder : deriv (frobeniusStickelbergerDetMulSigmaCube L w) 0 = 0 := by
    have h1 : deriv (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) 0 = -deriv (frobeniusStickelbergerDetMulSigmaCube L w) (-0) :=
      deriv_comp_neg (f := frobeniusStickelbergerDetMulSigmaCube L w) (x := 0)
    have h2 : (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) = frobeniusStickelbergerDetMulSigmaCube L w := funext (additionNumerator_neg L w ho)
    rw [h2, neg_zero] at h1
    linear_combination h1 / 2
  obtain ⟨p, hp⟩ := twistedGamma_analyticAt_zero L w he
  have hm := hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope
  refine ⟨dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0, ⟨_, hm⟩, fun y => ?_⟩
  have e1 := sub_smul_dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0 y
  have e2 := sub_smul_dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0 y
  rw [dslope_same, hder] at e2
  simp only [sub_zero, smul_eq_mul, hg0] at e1 e2
  rw [← e1, ← e2]
  ring
private lemma exists_analytic_eq_additionQuotient_near_zero (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ additionQuotient L w =ᶠ[𝓝[≠] 0] A := by
  obtain ⟨m, hm, hgm⟩ := exists_twistedGamma_eq_sq_mul_analytic L w he ho hz hs
  have hd : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := analyticAt_dslope L he
  have hd0 : dslope (wSigma L) 0 0 ≠ 0 := by
    rw [dslope_same, (hs L).1]
    exact one_ne_zero
  have hσ : ∀ y, wSigma L y = y * dslope (wSigma L) 0 y := fun y => by
    have := sub_smul_dslope (wSigma L) 0 y
    simp only [sub_zero, smul_eq_mul, sigma_zero L hz] at this
    exact this.symm
  refine ⟨fun y => m y / dslope (wSigma L) 0 y ^ 2, hm.div (hd.pow 2) (pow_ne_zero _ hd0), ?_⟩
  have hdne : ∀ᶠ y in 𝓝[≠] (0 : ℂ), dslope (wSigma L) 0 y ≠ 0 :=
    (hd.continuousAt.eventually_ne hd0).filter_mono nhdsWithin_le_nhds
  filter_upwards [additionQuotient_mul_eventuallyEq L w hz, hdne, self_mem_nhdsWithin] with y h1 h2 h3
  have hy : y ≠ 0 := h3
  rw [hgm, hσ y] at h1
  rw [eq_div_iff (pow_ne_zero _ h2)]
  apply mul_left_cancel₀ (pow_ne_zero 2 hy)
  linear_combination h1
end SigmaAdditionFormula
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple)
    (hq : SigmaQuasi) (hord : SigmaOrder) (z : ℂ) : 0 ≤ meromorphicOrderAt (additionQuotient L w) z := by
  by_cases hzL : z ∈ L.lattice
  · obtain ⟨A, hA, hfA⟩ := exists_analytic_eq_additionQuotient_near_zero L w he ho hz hs
    have hfun : additionQuotient L w = fun x => additionQuotient L w (x - z) := funext fun x => by
      have := additionQuotient_periodic L w hq (-z) (neg_mem hzL) x
      rw [← sub_eq_add_neg] at this
      exact this.symm
    have ht : Filter.Tendsto (fun x => x - z) (𝓝[≠] z) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_id.sub continuous_const).tendsto' z 0 (sub_self z)).mono_left
          nhdsWithin_le_nhds)
        (Filter.mem_of_superset self_mem_nhdsWithin fun x hx => sub_ne_zero.2 hx)
    have h2 : (fun x => additionQuotient L w (x - z)) =ᶠ[𝓝[≠] z] fun x => A (x - z) := ht.eventually hfA
    rw [hfun, meromorphicOrderAt_congr h2]
    exact (hA.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self z)).meromorphicOrderAt_nonneg
  · exact (additionQuotient_analyticAt L w he hz z hzL).meromorphicOrderAt_nonneg
end Formalism.L2.Th1.F.SigmaAdditionFormula
