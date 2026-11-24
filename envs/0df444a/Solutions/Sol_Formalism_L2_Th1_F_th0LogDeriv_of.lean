-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0LogDeriv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:14.462605+00:00
-- url     : https://prove2.me/submissions/bbe46a8b-0424-4239-aee0-f0caa7eca6c9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hl : SigmaLogDeriv) (he : EtaSplit) (hzq : ZetaQuasi)
    (hzo : ZetaOdd) : ThetaZeroLogDerivative := by
  intro L ω₀ z hω hn hzt
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn hzt ⊢
  have hζ : wZeta L t = s2 L * t + ((Real.pi : ℂ) / (area L : ℂ)) * conj t := by
    have h1 := hzq L (t + t) (-t) hω (by rwa [neg_mem_iff])
    rw [show -t + (t + t) = t by ring, hzo, he] at h1
    simp only [map_add] at h1
    linear_combination h1 / 2
  have hd1 : HasDerivAt (fun w => wSigma L (w + t)) (wZeta L (z + t) * wSigma L (z + t)) z := by
    have := (hl L (z + t) hzt).comp z ((hasDerivAt_id' z).add_const t)
    rw [mul_one] at this
    exact this
  have hg : HasDerivAt (fun w : ℂ => -(s2 L) * (w + t) ^ 2 / 2
        + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2))
      (-(s2 L) * (z + t) - (Real.pi : ℂ) * (conj t / (area L : ℂ))) z := by
    have e1 := ((((hasDerivAt_id' z).add_const t).mul ((hasDerivAt_id' z).add_const t)).const_mul
      (-(s2 L))).div_const 2
    have e2 := (((hasDerivAt_id' z).mul_const (conj t / (area L : ℂ))).const_mul
      (-(Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * herm L t t / 2)
    refine ((e1.add e2).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, herm]; ring
  have hfull := (hd1.mul hg.cexp).div_const (opU L t (sgStar L) 0)
  have hfun : th0 L t = fun w => wSigma L (w + t) * Complex.exp (-(s2 L) * (w + t) ^ 2 / 2
      + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) / opU L t (sgStar L) 0 := by
    funext w
    simp only [th0]
    congr 1
    simp only [opU, sgStar]
    rw [Complex.exp_add]; ring
  rw [hfun]
  refine hfull.congr_deriv ?_
  beta_reduce
  rw [hζ]; ring
end Formalism.L2.Th1.F
