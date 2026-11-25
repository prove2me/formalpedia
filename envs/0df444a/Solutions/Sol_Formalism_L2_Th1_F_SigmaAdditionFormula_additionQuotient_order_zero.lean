-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:10.356697+00:00
-- url     : https://prove2.me/submissions/c3011c79-07ae-4fd9-8702-e880c3672d93

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_analyticAt_dslope
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_sigma_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionNumerator_neg
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_analyticAt_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_mul_eventuallyEq
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
    (hord : SigmaOrder) : 0 ≤ meromorphicOrderAt (additionQuotient L w) 0 := by
  obtain ⟨A, hA, hfA⟩ := exists_analytic_eq_additionQuotient_near_zero L w he ho hz hs
  rw [meromorphicOrderAt_congr hfA]
  exact hA.meromorphicOrderAt_nonneg
end Formalism.L2.Th1.F.SigmaAdditionFormula
