-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:07:46.361255+00:00
-- url     : https://prove2.me/submissions/2de1d116-d16a-40b5-9e99-1fda63850fc2

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_gradient_continuousOn
import Theorems.Thm_AvramDividend_Classical_avram_ga_compact_interval_gradient_abs_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      y ∈ Icc a b → |deriv w y| ≤ K  := by
  have hCont :=
    avram_ga_original_finitecap_clip_gradient_continuousOn
      w C hC hFiniteCap hw δ hδ j
  simpa only [] using
    (avram_ga_compact_interval_gradient_abs_bound
      w (δ / 2)
      (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      hCont)
