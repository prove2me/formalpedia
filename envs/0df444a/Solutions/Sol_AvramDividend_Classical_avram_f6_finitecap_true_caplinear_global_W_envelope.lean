-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_finitecap_true_caplinear_global_W_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:56:40.844796+00:00
-- url     : https://prove2.me/submissions/a7c8e54d-8280-474f-a081-a129e74fc1b2

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_finitecap_true_caplinear_growth_envelope
set_option autoImplicit false
open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hbound : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (S z : ℝ) (hS : 0 ≤ S) (hzS : z ≤ S) :
    |if ENNReal.ofReal z ≤ C then w z
       else w C.toReal + (z - C.toReal)| ≤ K + S := by
  by_cases hz : 0 ≤ z
  · have hh := avram_f6_finitecap_true_caplinear_growth_envelope
      w C hC K hbound z hz
    linarith
  · have hneg : z < 0 := lt_of_not_ge hz
    have hz0 : ENNReal.ofReal z = 0 :=
      ENNReal.ofReal_eq_zero.mpr hneg.le
    have hK : 0 ≤ K := by
      have hh := hbound 0 le_rfl ENNReal.toReal_nonneg
      exact le_trans (abs_nonneg _) hh
    simp [hz0, hwneg z hneg]
    linarith
