-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_finitecap_original_downward_kink_firstorder_residual_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:10:24.18219+00:00
-- url     : https://prove2.me/submissions/45a1a589-a5f5-4599-92c8-845e74c032b7

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_rational_clip_gradient_ge_one
import Theorems.Thm_AvramDividend_Classical_avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (j : ℕ) (g x y : ℝ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let α : ℝ := deriv w b
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    V y - V x - (if x ≤ b then g else 1) * (y - x) ≤
      U y - U x - (if x ≤ b then g else α) * (y - x)  := by
  have hα :=
    avram_ga_original_finitecap_rational_clip_gradient_ge_one
      w C hC hFiniteCap hw_grad j
  simpa only [] using
    (avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
      w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      (deriv w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      g x y hα)
