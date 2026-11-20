-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_delayed_clock_real_min_tends_to_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:25:30.090274+00:00
-- url     : https://prove2.me/submissions/609bbebf-148a-4d32-981b-10f2b0289c4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (σ τ : ℝ≥0) (hστ : σ ≤ τ) :
    Tendsto (fun m : ℕ =>
      min (τ : ℝ) ((σ : ℝ) + (1 : ℝ) / ((m : ℝ) + 1)))
      atTop (𝓝 (σ : ℝ)) := by
  have hzero : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hright : Tendsto (fun m : ℕ =>
      (σ : ℝ) + (1 : ℝ) / ((m : ℝ) + 1))
      atTop (𝓝 (σ : ℝ)) := by
    convert (tendsto_const_nhds.add hzero) using 1 <;> simp
  have hleft : Tendsto (fun _ : ℕ => (τ : ℝ))
      atTop (𝓝 (τ : ℝ)) := tendsto_const_nhds
  have hmin := hleft.min hright
  have hle : (σ : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hστ
  simpa [min_eq_right hle] using hmin
