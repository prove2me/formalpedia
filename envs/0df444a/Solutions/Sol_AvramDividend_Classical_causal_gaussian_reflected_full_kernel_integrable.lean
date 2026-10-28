-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_reflected_full_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:42:44.406501+00:00
-- url     : https://prove2.me/submissions/1db129c7-3b84-48f4-8d90-f38782ea602a

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_full_kernel_local_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The finite-horizon Gaussian kernel remains integrable after causal reflection. -/
theorem solution
    (K : ℝ → ℝ) (β x : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun s : ℝ => β + K (x - s))
      (Ioc (0 : ℝ) x) volume := by
  by_cases hx : 0 ≤ x
  · have hInt : IntervalIntegrable (fun t : ℝ => β + K t) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
        (causal_l1_full_kernel_local_integrable K β x hK)
    have hRefl : IntervalIntegrable (fun s : ℝ => β + K (x - s)) volume 0 x := by
      simpa only [sub_zero, sub_self] using (hInt.comp_sub_left x).symm
    exact hRefl.1
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have he : Ioc (0 : ℝ) x = ∅ := Ioc_eq_empty_of_le hx'
    simp only [he]
    exact integrableOn_empty
