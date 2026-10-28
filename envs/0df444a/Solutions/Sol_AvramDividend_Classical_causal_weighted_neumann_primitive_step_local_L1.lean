-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_neumann_primitive_step_local_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:43:08.435533+00:00
-- url     : https://prove2.me/submissions/b59999fb-d642-4d4f-9853-265fe660d03f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exponential_twist_Ioc_convolution
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_local_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Untwist a signed convolution power and integrate it as a weighted primitive. -/
theorem solution
    (k P : ℝ → ℝ) (w x : ℝ) (hx : 0 < x)
    (hk : IntegrableOn (fun u : ℝ => Real.exp (w * u) * k u)
      (Ioc (0 : ℝ) x) volume)
    (hP : IntegrableOn (fun u : ℝ => Real.exp (w * u) * P u)
      (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      Real.exp (w * t) *
        (∫ s in Ioc (0 : ℝ) t, k s * P (t - s) ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * (x - s)) * k (x - s)) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P t ∂volume) ∂volume) := by
  let E : ℝ → ℝ := fun u => Real.exp (w * u) * k u
  let F : ℝ → ℝ := fun u => Real.exp (w * u) * P u
  have heval (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) x) :
      Real.exp (w * t) *
          (∫ s in Ioc (0 : ℝ) t, k s * P (t - s) ∂volume) =
        (∫ s in Ioc (0 : ℝ) t, E (t - s) * F s ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) t, E s * F (t - s) ∂volume := by
        simpa only [E, F] using
          causal_exponential_twist_Ioc_convolution k P w t
      _ = ∫ s in Ioc (0 : ℝ) t, E (t - s) * F s ∂volume :=
        (causal_convolution_time_reversal E F t ht.1.le).symm
  calc
    (∫ t in Ioc (0 : ℝ) x,
      Real.exp (w * t) *
        (∫ s in Ioc (0 : ℝ) t, k s * P (t - s) ∂volume) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        ∫ s in Ioc (0 : ℝ) t, E (t - s) * F s ∂volume) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact heval t ht
    _ = ∫ s in Ioc (0 : ℝ) x,
        E (x - s) * (∫ t in Ioc (0 : ℝ) s, F t ∂volume) ∂volume :=
      causal_l1_kernel_triangle_fubini_two_local_L1 E F x hx hk hP
    _ = ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * (x - s)) * k (x - s)) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P t ∂volume) ∂volume := rfl
