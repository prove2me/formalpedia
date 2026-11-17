-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_rational_clip_gradient_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:08:04.324586+00:00
-- url     : https://prove2.me/submissions/435f26bb-acff-4dc9-b05a-e7bbdbf7fe2e

import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    1 ≤ deriv w b  := by
  have hb :=
    avram_gbB41_original_finitecap_rational_clip_strict_interior
      C hC hFiniteCap j
  exact hw_grad _ hb.1 hb.2
