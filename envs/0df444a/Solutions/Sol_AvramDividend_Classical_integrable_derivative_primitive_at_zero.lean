-- Prove2me | solution 1 for AvramDividend.Classical.integrable_derivative_primitive_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:05:13.857505+00:00
-- url     : https://prove2.me/submissions/70debd62-fb0c-4d78-85aa-bff52aad0eb8

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (g k : ℝ → ℝ) (h0 : g 0 = 0)
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hk : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt g (k t) t) :
    ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x := by
  intro x hx
  have hint : IntervalIntegrable k volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2 (hk.mono_set Ioc_subset_Ioi_self)
  have := integral_eq_sub_of_hasDerivAt_of_le hx.le (hgcont.mono Icc_subset_Ici_self)
    (fun t ht => hderiv t ht.1) hint
  rw [intervalIntegral.integral_of_le hx.le] at this
  rw [this, h0, sub_zero]
