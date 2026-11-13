-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:16:19.97698+00:00
-- url     : https://prove2.me/submissions/653b2421-0c4c-4fa9-b03f-4c8114825226

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
import Theorems.Thm_AvramDividend_Classical_avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (Z : Ω → ℕ → ℝ)
    (hZ : ∀ i, Measurable (fun ω => Z ω i))
    (H : Ω → ℝ) (hHm : Measurable H) (hHI : Integrable H P) :
    Tendsto (fun k : ℕ =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Z ω i ∧ ENNReal.ofReal (Z ω i) < C) →
          Z ω i ∈ Icc (a k) (b k) then (0 : ℝ) else H ω) ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  let s : ℕ → Set Ω := fun k =>
    {ω | ∀ i < n + 1,
      (0 < Z ω i ∧ ENNReal.ofReal (Z ω i) < C) →
        Z ω i ∈ Icc (a k) (b k)}
  have hs (k : ℕ) : MeasurableSet (s k) := by
    dsimp [s]
    measurability
  have hEventual (ω : Ω) : ∀ᶠ k : ℕ in atTop, ω ∈ s k := by
    obtain ⟨N, hN⟩ :=
      avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
        C a b hExh n (Z ω)
    apply (eventually_ge_atTop N).mono
    intro k hk i hi hzi
    exact hN k hk i hi hzi
  have hAE : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ s k := by
    filter_upwards [] with ω
    exact hEventual ω
  have hTail := avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
    P H hHm hHI s hs hAE
  simpa only [s, Set.mem_setOf_eq] using hTail
