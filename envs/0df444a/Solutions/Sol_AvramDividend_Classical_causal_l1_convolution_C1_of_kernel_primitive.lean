-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_C1_of_kernel_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:41:24.592293+00:00
-- url     : https://prove2.me/submissions/431a188b-3f8e-49f8-b973-e74c21961d23

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_L1
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- A causal convolution with a positive-time L1 derivative kernel has C1 regularity. -/
theorem solution
    (f k g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f (x - s) * g s ∂volume) (Ioi (0 : ℝ)) := by
  let V : ℝ → ℝ := fun t =>
    ∫ s in Ioc (0 : ℝ) t, k (t - s) * f s ∂volume
  have hVcont : ContinuousOn V (Ioi (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_positive_of_Ici_input k f hkL1 hf
  have hVint : ∀ x : ℝ, 0 < x →
      IntervalIntegrable V volume 0 x := by
    intro x hx
    change IntegrableOn V (Ioc (0 : ℝ) x) volume ∧
      IntegrableOn V (Ioc x (0 : ℝ)) volume
    refine ⟨causal_l1_convolution_outer_integrable k f hkL1 hf x hx, ?_⟩
    simp [Ioc_eq_empty_of_le hx.le]
  have hC1 : ContDiffOn ℝ 1
      (fun x : ℝ => ∫ t in (0 : ℝ)..x, V t) (Ioi (0 : ℝ)) :=
    causal_positive_kernel_primitive_contDiff_one V hVcont hVint
  apply hC1.congr
  intro x hx
  change 0 < x at hx
  symm
  have hklocal : IntegrableOn k (Ioc (0 : ℝ) x) volume :=
    hkL1.mono_set (by intro y hy; exact hy.1)
  have htri :=
    causal_l1_kernel_triangle_fubini_two_L1 f k x hx hfL1 hklocal
  calc
    (∫ t in (0 : ℝ)..x, V t) =
      ∫ t in Ioc (0 : ℝ) x, V t ∂volume := by
        exact intervalIntegral.integral_of_le hx.le
    _ = ∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t,
            f (t - s) * k s ∂volume) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        change (∫ s in Ioc (0 : ℝ) t,
          k (t - s) * f s ∂volume) =
          ∫ s in Ioc (0 : ℝ) t,
            f (t - s) * k s ∂volume
        calc
          (∫ s in Ioc (0 : ℝ) t, k (t - s) * f s ∂volume) =
            ∫ s in Ioc (0 : ℝ) t, k s * f (t - s) ∂volume :=
              causal_convolution_time_reversal k f t ht.1.le
          _ = _ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with s
            exact mul_comm (k s) (f (t - s))
    _ = ∫ s in Ioc (0 : ℝ) x,
          f (x - s) * (∫ t in Ioc (0 : ℝ) s, k t ∂volume)
            ∂volume := htri
    _ = ∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [hg s hs.1]
