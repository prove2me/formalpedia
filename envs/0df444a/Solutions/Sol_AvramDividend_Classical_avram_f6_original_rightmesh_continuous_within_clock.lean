-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_rightmesh_continuous_within_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:02:53.980992+00:00
-- url     : https://prove2.me/submissions/2b6df3cb-4f4a-4c66-a467-01520a8edfa5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (σ τ : ℝ≥0) (hστ : σ ≤ τ)
    (f : ℝ≥0 → ℝ)
    (hf : ContinuousWithinAt f (Ici σ) σ) :
    Tendsto (fun m : ℕ =>
      f (min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))))
      atTop (𝓝 (f σ)) := by
  let ρ : ℕ → ℝ≥0 := fun m =>
    min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
  have hReal : Tendsto (fun m => (ρ m : ℝ)) atTop (𝓝 (σ : ℝ)) := by
    simpa only [ρ, NNReal.coe_min, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_natCast] using
      avram_f6_original_delayed_clock_real_min_tends_to_stopped σ τ hστ
  have hClock : Tendsto ρ atTop (𝓝 σ) :=
    NNReal.tendsto_coe.mp hReal
  have hLower (m : ℕ) : σ ≤ ρ m := by
    dsimp [ρ]
    exact le_min hστ (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _))
  have hWithin : Tendsto ρ atTop (𝓝[Set.Ici σ] σ) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hClock, Filter.Eventually.of_forall (fun m => hLower m)⟩
  simpa only [Function.comp_def, ρ] using hf.tendsto.comp hWithin
