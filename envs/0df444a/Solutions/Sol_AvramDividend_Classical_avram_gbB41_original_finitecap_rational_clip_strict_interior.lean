-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB41_original_finitecap_rational_clip_strict_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:01:48.576434+00:00
-- url     : https://prove2.me/submissions/fb181cd0-f4da-4c59-ae00-8ef5b18265c5

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_interior_finite_cap_fraction_strict_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 < b ∧ ENNReal.ofReal b < C := by
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hCapPos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hb := avram_gbB39_interior_finite_cap_fraction_strict_band
    C.toReal hCapPos j
  refine ⟨hb.1, ?_⟩
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hb.1) hFiniteCap).2 hb.2
