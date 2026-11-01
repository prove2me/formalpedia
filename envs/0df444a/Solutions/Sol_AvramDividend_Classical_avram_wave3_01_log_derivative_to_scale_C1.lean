-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_log_derivative_to_scale_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:23:24.185792+00:00
-- url     : https://prove2.me/submissions/0f695450-91f2-4512-8b06-a445cbfd4a55

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_derivative_to_c1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Filter
open scoped Topology

/-- A continuous logarithmic derivative makes a positive scale function C¹. -/
theorem solution
    (W κ : ℝ → ℝ)
    (hWpos : ∀ a : ℝ, 0 < a → 0 < W a)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hlog : ∀ a : ℝ, 0 < a →
      HasDerivAt (fun x : ℝ => Real.log (W x)) (κ a) a) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hWderiv : ∀ a : ℝ, 0 < a →
      HasDerivAt W (W a * κ a) a := by
    intro a ha
    have hE : HasDerivAt (fun x : ℝ => Real.exp (Real.log (W x)))
        (Real.exp (Real.log (W a)) * κ a) a := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (Real.log (W a))).comp a (hlog a ha)
    have heq : W =ᶠ[𝓝 a] (fun x : ℝ => Real.exp (Real.log (W x))) := by
      filter_upwards [isOpen_Ioi.mem_nhds ha] with x hx
      exact (Real.exp_log (hWpos x hx)).symm
    have hE' := hE.congr_of_eventuallyEq heq
    simpa only [Real.exp_log (hWpos a ha)] using hE'
  have hWcont : ContinuousOn W (Ioi (0 : ℝ)) := by
    intro a ha
    exact (hWderiv a ha).continuousAt.continuousWithinAt
  have hprod : ContinuousOn (fun x : ℝ => W x * κ x) (Ioi (0 : ℝ)) :=
    hWcont.mul hκ
  exact avram_wave3_01_continuous_derivative_to_c1
    W (fun x : ℝ => W x * κ x) hprod hWderiv
