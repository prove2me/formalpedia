-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite56_cap_fraction_cutoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:52:27.738595+00:00
-- url     : https://prove2.me/submissions/e9302d9a-f855-426b-a554-7e1e1dbd3d91

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

theorem solution (c : ℝ) :
    Tendsto
      (fun j : ℕ => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      atTop (𝓝 c) := by
  let b : ℕ → ℝ :=
    fun j => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let eps : ℕ → ℝ := fun j => (1 : ℝ) / ((j : ℝ) + 1)
  have hSmall : Tendsto eps atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hDen : Tendsto (fun j => 1 + eps j) atTop (𝓝 (1 : ℝ)) := by
    convert tendsto_const_nhds.add hSmall using 1 <;> simp [eps]
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hRatio : Tendsto (fun j => (1 : ℝ) / (1 + eps j))
      atTop (𝓝 (1 : ℝ)) := by
    convert (hOne.div hDen (by norm_num : (1 : ℝ) ≠ 0)) using 1
      <;> first | rfl | (funext j; rfl) | norm_num
  have hb : Tendsto b atTop (𝓝 c) := by
    convert tendsto_const_nhds.mul hRatio using 1
    · funext j
      dsimp [b, eps]
      have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have hj2 : (j : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · ring
  exact hb
