-- Prove2me | solution 1 for AvramDividend.Classical.avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:42:23.553059+00:00
-- url     : https://prove2.me/submissions/846ab749-b7fe-4180-abaf-48dbd2c32ad3

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (i : ℕ → Ω → ℕ)
    (hCell : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      s ∈ Set.Icc 0 (n : ℝ≥0) ∧
        ρ ω ∈ Set.Icc 0 (n : ℝ≥0) ∧
        dist s (ρ ω) ≤ (Δ : ℝ)  := by
  intro m ω
  dsimp
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
  have hLow : s ≤ ρ ω := (hCell m ω).1
  have hHigh : ρ ω ≤ s + Δ := (hCell m ω).2
  have hSBound : s ≤ (n : ℝ≥0) := le_trans hLow (hρ ω)
  have hSreal : (s : ℝ) ≤ (ρ ω : ℝ) := by
    exact_mod_cast hLow
  have hDreal : (ρ ω : ℝ) ≤ (s : ℝ) + (Δ : ℝ) := by
    exact_mod_cast hHigh
  refine ⟨⟨bot_le, hSBound⟩, ⟨bot_le, hρ ω⟩, ?_⟩
  rw [NNReal.dist_eq]
  rw [abs_of_nonpos (sub_nonpos.mpr hSreal)]
  have hDiff : (ρ ω : ℝ) - (s : ℝ) ≤ (Δ : ℝ) := by
    linarith [hDreal]
  simpa only [neg_sub, Δ, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_natCast, NNReal.coe_one] using hDiff
