-- Prove2me | solution 1 for AvramDividend.Classical.bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:04:08.963397+00:00
-- url     : https://prove2.me/submissions/73ae8aa2-5a7a-4b6d-a538-69184b22cca7

import Mathlib

open Filter Topology
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*}
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0∞)
    (T : ℝ≥0)
    (hEnn : ∀ ω : Ω, Tendsto
      (fun n : ℕ => (grid n ω : ℝ≥0∞)) atTop
      (𝓝 (raw ω ⊓ (T : ℝ≥0∞))))
    (hAbove : ∀ (ω : Ω) (n : ℕ),
      raw ω ⊓ (T : ℝ≥0∞) ≤ (grid n ω : ℝ≥0∞)) :
    (∀ ω : Ω, Tendsto (fun n : ℕ => grid n ω) atTop
      (𝓝 ((raw ω ⊓ (T : ℝ≥0∞)).toNNReal))) ∧
    (∀ (ω : Ω) (n : ℕ),
      (raw ω ⊓ (T : ℝ≥0∞)).toNNReal ≤ grid n ω) := by
  have hne : ∀ ω, raw ω ⊓ (T : ℝ≥0∞) ≠ ⊤ :=
    fun ω => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  refine ⟨fun ω => ?_, fun ω n => ?_⟩
  · have := (ENNReal.tendsto_toNNReal (hne ω)).comp (hEnn ω)
    simpa [Function.comp_def] using this
  · have := ENNReal.toNNReal_mono ENNReal.coe_ne_top (hAbove ω n)
    simpa using this
