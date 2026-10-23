-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_triangle_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:58:47.402018+00:00
-- url     : https://prove2.me/submissions/7df022ae-2e64-4ad5-b8f0-d6b03aff4618

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_open_indicator_inner_identity
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_time_primitive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrating a causal L1 convolution commutes with taking a primitive. -/
theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by
  let G : ℝ → ℝ := fun t => ∫ s in Ioc (0 : ℝ) t, g s ∂volume
  calc
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) ∂volume) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact causal_convolution_time_reversal K g t ht.1.le
    _ = (∫ t in Ioc (0 : ℝ) x,
      (∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact causal_open_indicator_inner_identity K g t x ht.1.le ht.2
    _ = (∫ u in Ioc (0 : ℝ) x, K u * G (x - u) ∂volume) := by
          simpa only [G] using
            causal_l1_truncated_convolution_time_primitive K g hK hg x hx
    _ = (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
          exact (causal_convolution_time_reversal K G x hx.le).symm
    _ = (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := rfl
