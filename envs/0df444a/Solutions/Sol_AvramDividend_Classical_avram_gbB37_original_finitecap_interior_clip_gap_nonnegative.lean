-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:34:10.163829+00:00
-- url     : https://prove2.me/submissions/db529d15-5985-47a1-8f0d-341e66068a7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 ≤ b ∧ b ≤ C.toReal ∧
      0 ≤ (w C.toReal - w b) - (C.toReal - b) := by
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hCapPos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbC : b ≤ C.toReal := by
    have hf : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_succ (j + 1)
    dsimp [b]
    nlinarith [mul_nonneg (le_of_lt hCapPos) (sub_nonneg.mpr hf)]
  have hcap : ENNReal.ofReal C.toReal ≤ C := by
    simpa using le_of_eq (ENNReal.ofReal_toReal hFiniteCap)
  have hSec :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hw_cont hw_smooth hw_grad b C.toReal hb0 hbC hcap
  refine ⟨hb0, hbC, ?_⟩
  linarith
