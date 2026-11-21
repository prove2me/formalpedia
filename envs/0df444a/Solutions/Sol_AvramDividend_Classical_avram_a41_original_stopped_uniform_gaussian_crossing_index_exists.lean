-- Prove2me | solution 1 for AvramDividend.Classical.avram_a41_original_stopped_uniform_gaussian_crossing_index_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:51:28.559177+00:00
-- url     : https://prove2.me/submissions/8f7e85bb-b01c-4375-b1f5-e6e2e6c6c60a

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    ∃ i : ℕ → Ω → ℕ, ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ := by
  refine ⟨fun m ω => ⌊ρ ω / ((n : ℝ≥0) / ((m : ℝ≥0) + 1))⌋₊, ?_⟩
  intro m ω
  dsimp
  set Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  have hn0 : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hΔ : 0 < Δ := div_pos hn0 (by positivity)
  have hfloor : (⌊ρ ω / Δ⌋₊ : ℝ≥0) ≤ ρ ω / Δ :=
    Nat.floor_le (by positivity)
  have hfloor' : ρ ω / Δ < (⌊ρ ω / Δ⌋₊ : ℝ≥0) + 1 :=
    Nat.lt_floor_add_one _
  constructor
  · have h : (⌊ρ ω / Δ⌋₊ : ℝ≥0) * Δ ≤ ρ ω :=
      (le_div_iff₀ hΔ).mp hfloor
    simpa only [Δ] using h
  · have h : ρ ω < ((⌊ρ ω / Δ⌋₊ : ℝ≥0) + 1) * Δ :=
      (div_lt_iff₀ hΔ).mp hfloor'
    have hh : ρ ω ≤ (⌊ρ ω / Δ⌋₊ : ℝ≥0) * Δ + Δ := by
      nlinarith
    simpa only [Δ] using hh
