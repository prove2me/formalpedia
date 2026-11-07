-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:03:59.23609+00:00
-- url     : https://prove2.me/submissions/9f848400-7ef8-4fda-9c7e-c3c4fd80c457

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A uniformly controlled C¹ finite-cap cutoff error vanishes along ANY
nonnegative reserve path sequence, including cap contact and overshoots.
No derivative at the cap is assumed. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbC : ∀ n, b n ≤ C.toReal)
    (hb : Tendsto b atTop (𝓝 C.toReal))
    (hy : ∀ n, 0 ≤ y n) :
    Tendsto (fun n => (if y n ≤ C.toReal then w (y n)
      else w C.toReal + (y n - C.toReal)) -
      (if y n ≤ b n then w (y n)
       else w (b n) + (y n - b n)))
      atTop (𝓝 (0 : ℝ)) := by
  have hcReal : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hfinite
  have hDef :=
    avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
      w C.toReal hcReal hw_cont b hb
  have hLow : ∀ n, 0 ≤ (if y n ≤ C.toReal then w (y n)
      else w C.toReal + (y n - C.toReal)) -
      (if y n ≤ b n then w (y n)
       else w (b n) + (y n - b n)) := by
    intro n
    exact (avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
      C hC hfinite w hw_cont hw_smooth hw_grad
      (b n) (y n) (hb0 n) (hbC n) (hy n)).1
  have hUpper : ∀ n, (if y n ≤ C.toReal then w (y n)
      else w C.toReal + (y n - C.toReal)) -
      (if y n ≤ b n then w (y n)
       else w (b n) + (y n - b n)) ≤
      (w C.toReal - w (b n)) - (C.toReal - b n) := by
    intro n
    exact (avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
      C hC hfinite w hw_cont hw_smooth hw_grad
      (b n) (y n) (hb0 n) (hbC n) (hy n)).2
  exact squeeze_zero hLow hUpper hDef
