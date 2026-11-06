-- Prove2me | solution 1 for BianchiIX.integral_le_of_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:48:20.837285+00:00
-- url     : https://prove2.me/submissions/2c6c7c9e-096b-4f21-be98-7a5e49352018

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory


theorem solution {f f' g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ContinuousOn g (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f' t ≤ -c * g t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, g t) ≤ f a / c := by
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) := (hf t ht).neg.div_const c
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    hg.integrableOn_Icc (fun t ht => ?_)
  · apply H.trans
    have hbc : 0 ≤ f b / c := div_nonneg hfb hc.le
    simp only [Pi.neg_apply, neg_div]
    linarith only [hbc]
  · apply (le_div_iff₀ hc).mpr
    nlinarith only [hbound t (Ioo_subset_Icc_self ht)]
