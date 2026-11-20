-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:57:37.918501+00:00
-- url     : https://prove2.me/submissions/9d6de4cc-b09a-4baa-9232-900fd020f8b3

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_clipped_mesh_width
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (n j i : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (hcross : min (((i + 1 : ℕ) : ℝ≥0) /
      ((j + 1 : ℕ) : ℝ≥0)) t = t) :
    t ≤ min ((i : ℝ≥0) /
      ((j + 1 : ℕ) : ℝ≥0)) t +
      (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
  have hw :=
    avram_jump6_B_canonical_clipped_mesh_width j i t
  rw [hcross] at hw
  have hn1 : (1 : ℝ≥0) ≤ (n : ℝ≥0) := by
    exact_mod_cast hn
  have hfrac :
      (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) ≤
      (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
    gcongr
  exact hw.trans (add_le_add_right hfrac _)
