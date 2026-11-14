-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb29_original_zero_contact_stopped_K_uniform_prefix_limit_from_exact_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:23.625351+00:00
-- url     : https://prove2.me/submissions/36d60a83-a0b5-4f6f-88b1-c0124edb192c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T w0 mass : ℝ) (hT : 0 < T)
    (K : ℕ → ℝ)
    (hK : ∀ n, K n = -(w0 * mass) *
      (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))) :
    Tendsto K atTop
      (𝓝 (-(w0 * mass) *
        (∫ t in Ioc (0 : ℝ) T,
          Real.exp (-(q * t)) ∂(volume : Measure ℝ))))  := by
  have hFun : K = (fun n : ℕ => -(w0 * mass) *
        (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
          Real.exp (-(q * t)) ∂(volume : Measure ℝ))) := by
    funext n
    exact hK n
  rw [hFun]
  exact (avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
    q T hT).const_mul (-(w0 * mass))
