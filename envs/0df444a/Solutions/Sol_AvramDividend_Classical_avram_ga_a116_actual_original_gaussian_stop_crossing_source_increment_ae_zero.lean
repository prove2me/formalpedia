-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a116_actual_original_gaussian_stop_crossing_source_increment_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:01:53.052313+00:00
-- url     : https://prove2.me/submissions/08da72d5-45c8-432e-917d-ec7a0f46f1d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- True random physical stop crossing clock has vanishing original Gaussian source displacement almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) (i : ℕ → Ω → ℕ)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hCross : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (0 : ℝ)) := by
  let Δ : ℕ → ℝ≥0 := fun m =>
    (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → Ω → ℝ≥0 := fun m ω => (i m ω : ℝ≥0) * Δ m
  let t : ℕ → Ω → ℝ≥0 := fun _ ω => ρ ω
  have hR : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 (n : ℝ≥0) ∧
        t m ω ∈ Icc 0 (n : ℝ≥0) := by
    filter_upwards [] with ω
    intro m
    have hs : s m ω < t m ω := (hCross m ω).1
    exact ⟨⟨by positivity, (le_of_lt hs).trans (hρ ω)⟩,
      ⟨by positivity, hρ ω⟩⟩
  have hG : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤
        (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by
    filter_upwards [] with ω
    intro m
    have hs : s m ω < t m ω := (hCross m ω).1
    have hc : t m ω ≤ s m ω + Δ m := (hCross m ω).2
    have h1 : (s m ω : ℝ) ≤ (t m ω : ℝ) :=
      NNReal.coe_le_coe.mpr (le_of_lt hs)
    have h2 : (t m ω : ℝ) ≤ (s m ω : ℝ) + (Δ m : ℝ) := by
      have h := NNReal.coe_le_coe.mpr hc
      simpa only [NNReal.coe_add] using h
    change dist (s m ω) (t m ω) ≤ (Δ m : ℝ)
    rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr h1)]
    linarith
  simpa only [s, t, Δ] using
    (avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
      X hν (n : ℝ≥0) s t hR hG)
