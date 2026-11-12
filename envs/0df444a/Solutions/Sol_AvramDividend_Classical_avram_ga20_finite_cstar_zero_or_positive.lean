-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga20_finite_cstar_zero_or_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:59:44.12928+00:00
-- url     : https://prove2.me/submissions/12b84ae2-0f7c-4f99-9fc3-eb55ee42f734

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite scale-function barrier is either zero or strictly positive. -/
theorem solution (W : ℝ → ℝ) (hc : cstar W < ⊤) :
    cstar W = 0 ∨ 0 < cstar W := by
  by_cases hzero : cstar W = 0
  · exact Or.inl hzero
  · exact Or.inr (pos_iff_ne_zero.mpr hzero)
