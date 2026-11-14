-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a117_actual_original_gaussian_full_crossing_cell_source_increment_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:21:43.507087+00:00
-- url     : https://prove2.me/submissions/3d2a54e7-4c64-4eb7-88b1-5263be977b02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The true full physical original Gaussian source increment across an arbitrarily randomly selected cell inside the horizon vanishes a.s. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      (i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
      X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (0 : ℝ)) := by
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → Ω → ℝ≥0 := fun m ω => (i m ω : ℝ≥0) * Δ m
  let t : ℕ → Ω → ℝ≥0 := fun m ω => s m ω + Δ m
  have hR : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 (n : ℝ≥0) ∧
        t m ω ∈ Icc 0 (n : ℝ≥0) := by
    filter_upwards [] with ω
    intro m
    have h := hEnd m ω
    change t m ω ≤ (n : ℝ≥0) at h
    have hs : s m ω ≤ t m ω := by
      change s m ω ≤ s m ω + Δ m
      exact le_add_of_nonneg_right (by positivity)
    exact ⟨⟨by positivity, hs.trans h⟩, ⟨by positivity, h⟩⟩
  have hG : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤
        (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by
    filter_upwards [] with ω
    intro m
    change dist (s m ω) (s m ω + Δ m) ≤ (Δ m : ℝ)
    rw [NNReal.dist_eq, NNReal.coe_add]
    have hs : (s m ω : ℝ) - ((s m ω : ℝ) + (Δ m : ℝ)) ≤ 0 := by
      have hd : 0 ≤ (Δ m : ℝ) := (Δ m).property
      linarith
    rw [abs_of_nonpos hs]
    linarith
  simpa only [s, t, Δ] using
    (avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
      X hν (n : ℝ≥0) s t hR hG)
