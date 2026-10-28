-- Prove2me | solution 1 for AvramDividend.Classical.causal_local_fubini_C1_of_convolution_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:09:42.278184+00:00
-- url     : https://prove2.me/submissions/07b2fbe8-0650-4363-b3da-631e011297e8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_local_L1
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (f k g : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → IntegrableOn f (Ioc (0 : ℝ) x) volume)
    (hk : ∀ x : ℝ, 0 < x → IntegrableOn k (Ioc (0 : ℝ) x) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, k s ∂volume) = g x)
    (J : ℝ → ℝ)
    (hJ : ∀ x : ℝ, 0 < x →
      J x = ∫ s in Ioc (0 : ℝ) x, f (x - s) * k s ∂volume)
    (hJcont : ContinuousOn J (Ioi (0 : ℝ)))
    (hJint : ∀ x : ℝ, 0 < x → IntervalIntegrable J volume 0 x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
      (Ioi (0 : ℝ)) := by
  have hJprimitive := causal_positive_kernel_primitive_contDiff_one J hJcont hJint
  apply hJprimitive.congr
  intro x hx
  have hx0 : 0 < x := hx
  rw [intervalIntegral.integral_of_le (le_of_lt hx0)]
  symm
  calc
    (∫ t in Ioc (0 : ℝ) x, J t ∂volume) =
        (∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t, f (t - s) * k s ∂volume) ∂volume) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact hJ t ht.1
    _ = (∫ s in Ioc (0 : ℝ) x,
        f (x - s) * (∫ t in Ioc (0 : ℝ) s, k t ∂volume) ∂volume) :=
        causal_l1_kernel_triangle_fubini_two_local_L1 f k x hx0 (hf x hx0) (hk x hx0)
    _ = (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        change f (x - s) * (∫ t in Ioc (0 : ℝ) s, k t ∂volume) =
          f (x - s) * g s
        rw [hg s hs.1]
    _ = (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) :=
        causal_convolution_time_reversal f g x (le_of_lt hx0)
