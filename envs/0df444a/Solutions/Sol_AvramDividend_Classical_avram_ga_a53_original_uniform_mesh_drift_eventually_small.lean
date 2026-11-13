-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a53_original_uniform_mesh_drift_eventually_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:23:51.796203+00:00
-- url     : https://prove2.me/submissions/1c744fce-651c-4f0a-b207-0b114b24b01a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Original zero-jump Gaussian physical-mesh drift is eventually below any positive threshold. -/
theorem solution (n : ℕ) (c η : ℝ) (hη : 0 < η) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∀ᶠ m : ℕ in atTop, |((Δ m : ℝ) * c)| ≤ η / 2 := by
  dsimp
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  change ∀ᶠ m : ℕ in atTop, |((Δ m : ℝ) * c)| ≤ η / 2
  have hWidth : Tendsto Δ atTop (𝓝 (0 : ℝ≥0)) := by
    simpa only [Δ] using
      (avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero n)
  have hReal : Tendsto (fun m : ℕ => (Δ m : ℝ)) atTop
      (𝓝 (0 : ℝ)) :=
    NNReal.tendsto_coe.mpr hWidth
  have hDrift : Tendsto (fun m : ℕ => ((Δ m : ℝ) * c))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hReal.mul_const c
  have hAbs : Tendsto (fun m : ℕ => |((Δ m : ℝ) * c)|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using hDrift.abs
  exact hAbs.eventually_le_const (by linarith : (0 : ℝ) < η / 2)
