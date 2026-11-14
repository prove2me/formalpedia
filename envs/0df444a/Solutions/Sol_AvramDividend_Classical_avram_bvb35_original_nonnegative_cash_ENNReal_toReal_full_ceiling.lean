-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb35_original_nonnegative_cash_ENNReal_toReal_full_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:30.195497+00:00
-- url     : https://prove2.me/submissions/b36ba1bd-e0b8-4bae-a491-993999d53828

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (cash : ℝ≥0∞) (w m c e : ℝ)
    (hw : 0 ≤ w) (hm : 0 ≤ m) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hHJB : cash + ENNReal.ofReal (e * w) ≤
      ENNReal.ofReal (w + m * w * c)) :
    cash.toReal + e * w ≤ w + m * w * c  := by
  have hA : 0 ≤ w + m * w * c := by positivity
  have hE : 0 ≤ e * w := mul_nonneg he hw
  have hRHS : ENNReal.ofReal (w + m * w * c) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hCashLE : cash ≤ ENNReal.ofReal (w + m * w * c) := by
    calc
      cash ≤ cash + ENNReal.ofReal (e * w) := by
        exact le_add_of_nonneg_right (zero_le : 0 ≤ ENNReal.ofReal (e * w))
      _ ≤ _ := hHJB
  have hCashFin : cash ≠ ⊤ :=
    ne_top_of_le_ne_top hRHS hCashLE
  have hTermFin : ENNReal.ofReal (e * w) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hToReal := ENNReal.toReal_mono hRHS hHJB
  rw [ENNReal.toReal_add hCashFin hTermFin,
    ENNReal.toReal_ofReal hE, ENNReal.toReal_ofReal hA] at hToReal
  exact hToReal
