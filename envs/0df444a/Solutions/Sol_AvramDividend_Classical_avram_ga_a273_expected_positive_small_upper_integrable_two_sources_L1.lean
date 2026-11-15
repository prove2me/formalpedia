-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:15:25.817249+00:00
-- url     : https://prove2.me/submissions/dd5bf037-77b6-4ddb-b74b-546111f519e6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F G H : ℕ → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hFInt : ∀ m, Integrable (F m) P)
    (hGInt : ∀ m, Integrable (G m) P)
    (hHInt : ∀ m, Integrable (H m) P)
    (hFPos : ∀ m ω, 0 ≤ F m ω)
    (hBound : ∀ m ω, F m ω ≤ G m ω+c*H m ω)
    (hGLim : Tendsto (fun m => ∫ ω, G m ω ∂P) atTop (𝓝 (0:ℝ)))
    (hHLim : Tendsto (fun m => ∫ ω, H m ω ∂P) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0:ℝ)) := by
  have hUpper (m : ℕ) :
      (∫ ω, F m ω ∂P) ≤
        (∫ ω, G m ω ∂P) + c * (∫ ω, H m ω ∂P) := by
    calc
      (∫ ω, F m ω ∂P) ≤ (∫ ω, G m ω + c * H m ω ∂P) :=
        integral_mono (hFInt m)
          ((hGInt m).add ((hHInt m).const_mul c)) (hBound m)
      _ = (∫ ω, G m ω ∂P) + c * (∫ ω, H m ω ∂P) := by
        rw [integral_add (hGInt m) ((hHInt m).const_mul c)]
        rw [integral_const_mul]
  have hLimit : Tendsto (fun m =>
      (∫ ω, G m ω ∂P) + c * (∫ ω, H m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, add_zero, zero_add] using hGLim.add (hHLim.const_mul c)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hLimit
    (Filter.Eventually.of_forall (fun m =>
      integral_nonneg (hFPos m)))
    (Filter.Eventually.of_forall hUpper)
