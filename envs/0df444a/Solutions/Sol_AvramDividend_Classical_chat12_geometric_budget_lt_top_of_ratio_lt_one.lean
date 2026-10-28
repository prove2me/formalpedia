-- Prove2me | solution 1 for AvramDividend.Classical.chat12_geometric_budget_lt_top_of_ratio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:52:57.591432+00:00
-- url     : https://prove2.me/submissions/ded651c0-2d57-4613-a4aa-18de1225f90c

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) (hp1 : p < 1) :
    ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ < ∞ := by
  have hOne : ENNReal.ofReal p < 1 :=
    ENNReal.ofReal_lt_one.mpr hp1
  have hGap : 0 < 1 - ENNReal.ofReal p :=
    tsub_pos_iff_lt.mpr hOne
  have hInv : (1 - ENNReal.ofReal p)⁻¹ < ∞ :=
    ENNReal.inv_lt_top.mpr hGap
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInv
