-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:51:17.321594+00:00
-- url     : https://prove2.me/submissions/461d7f19-2558-4513-88ad-2f9e120519f0

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) :
    Tendsto (fun j : ℕ =>
      (w C.toReal -
        w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal -
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (𝓝 (0 : ℝ)) := by
  have hc : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have hRatio : Tendsto
      (fun j : ℕ => (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    have hBase : Tendsto (fun n : ℕ => (n : ℝ) / (n + (1 : ℝ)))
        atTop (𝓝 (1 : ℝ)) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    have hShift := hBase.comp (tendsto_add_atTop_nat 1)
    convert hShift using 1
    ext j
    push_cast
    congr 1 <;> norm_num [Nat.cast_add] <;> ring
  have hB : Tendsto
      (fun j : ℕ => C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      atTop (𝓝 C.toReal) := by
    simpa only [mul_one] using (tendsto_const_nhds.mul hRatio :
      Tendsto (fun j : ℕ => C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      atTop (𝓝 (C.toReal * 1)))
  exact avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
    w C.toReal hc hw_cont
    (fun j : ℕ => C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) hB
