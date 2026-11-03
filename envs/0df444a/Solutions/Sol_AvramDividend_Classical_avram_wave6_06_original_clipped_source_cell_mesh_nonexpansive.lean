-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:30:23.437198+00:00
-- url     : https://prove2.me/submissions/f9db9b11-1154-47bb-bbe6-4707d13f300b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Clipping an original increasing clock at a fixed stopping time cannot
    enlarge one real-valued mesh increment. -/
theorem solution
    (u : ℕ → ℝ≥0) (hu : Monotone u) (i : ℕ) (τ : ℝ≥0)
    (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m) :
    ((min (u (i + 1)) τ : ℝ) - (min (u i) τ : ℝ)) ≤ m := by
  have hstep : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  change min (u (i + 1) : ℝ) (τ : ℝ) -
    min (u i : ℝ) (τ : ℝ) ≤ m
  rcases le_total (u i) τ with ha | ha
  · have har : (u i : ℝ) ≤ (τ : ℝ) := by exact_mod_cast ha
    rcases le_total (u (i + 1)) τ with hb | hb
    · have hbr : (u (i + 1) : ℝ) ≤ (τ : ℝ) := by
        exact_mod_cast hb
      rw [min_eq_left hbr, min_eq_left har]
      exact hmesh
    · have hbr : (τ : ℝ) ≤ (u (i + 1) : ℝ) := by
        exact_mod_cast hb
      rw [min_eq_right hbr, min_eq_left har]
      exact le_trans (sub_le_sub_right hbr _) hmesh
  · have hb : τ ≤ u (i + 1) := le_trans ha hstep
    have har : (τ : ℝ) ≤ (u i : ℝ) := by exact_mod_cast ha
    have hbr : (τ : ℝ) ≤ (u (i + 1) : ℝ) := by
      exact_mod_cast hb
    rw [min_eq_right hbr, min_eq_right har]
    simpa using hm

