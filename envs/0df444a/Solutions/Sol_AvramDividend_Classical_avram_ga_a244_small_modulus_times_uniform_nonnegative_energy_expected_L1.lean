-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a244_small_modulus_times_uniform_nonnegative_energy_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:28.882193+00:00
-- url     : https://prove2.me/submissions/782ec1ff-3910-4daf-8284-586da7ad8d59

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (ε : ℕ → ℝ) (K : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hBound : ∀ m, (∫ ω, F m ω ∂P) ≤ K)
    (hε : ∀ m, 0 ≤ ε m)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, ε m * F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hUpper (m : ℕ) :
      (∫ ω, ε m * F m ω ∂P) ≤ ε m * K := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hBound m) (hε m)
  have hLower (m : ℕ) :
      0 ≤ (∫ ω, ε m * F m ω ∂P) :=
    integral_nonneg (fun ω => mul_nonneg (hε m) (hFpos m ω))
  have hTop : Tendsto (fun m => ε m * K) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hεlim.mul_const K
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hTop
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper)
