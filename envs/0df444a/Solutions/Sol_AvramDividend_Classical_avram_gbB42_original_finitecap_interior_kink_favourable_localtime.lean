-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB42_original_finitecap_interior_kink_favourable_localtime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:49:14.432163+00:00
-- url     : https://prove2.me/submissions/0b2ba034-b679-4b03-9e2c-27e4eb3e15f3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite53_original_interior_C2_derivative_certificates
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb0 : 0 < b) (hbC : ENNReal.ofReal b < C) :
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by
  obtain ⟨hDer, _⟩ :=
    avram_gfinite53_original_interior_C2_derivative_certificates
      w C hw_smooth b hb0 hbC
  exact avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
    w b hDer.differentiableAt (hw_grad b hb0 hbC)
