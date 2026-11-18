-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:41:24.957175+00:00
-- url     : https://prove2.me/submissions/53a64c93-359d-4f67-97b1-252f37ff75e8

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Topology
open MeasureTheory Filter
noncomputable section
/-- Restrict a globally convergent L1 physical-grid noise to a future Gaussian event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℝ) (N : Ω → ℝ)
    (hInt : ∀ m, Integrable (fun ω => |N ω - M m ω|) P)
    (hL1 : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hNonneg (m : ℕ) :
      0 ≤ ∫ ω in A, |N ω - M m ω| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hUpper (m : ℕ) :
      (∫ ω in A, |N ω - M m ω| ∂P) ≤
      ∫ ω, |N ω - M m ω| ∂P :=
    setIntegral_le_integral (hInt m)
      (Eventually.of_forall (fun ω => abs_nonneg _))
  exact squeeze_zero hNonneg hUpper hL1
