-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a118_actual_stopped_gaussian_true_crossing_uniform_value_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:21:56.220222+00:00
-- url     : https://prove2.me/submissions/d103cf70-a90d-4b17-a106-df48964a0270

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The actual original Gaussian stopped crossing source value has vanishing expected absolute L1 for every bounded uniformly continuous compact-truncated value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) (i : ℕ → Ω → ℕ)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hCross : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ)
    (w : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ z : ℝ, |w z| ≤ M)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, |v - u| < δ → |w v - w u| < ε)
    (y : ℕ → Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)) -
        w (y m ω)|) P) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by
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
    (avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
      X hν (n : ℝ≥0) s t hR hG w M hM hW hmod y hMeas)
