-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_closed_cash_ennreal_budget_toReal_signed_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:41:18.853584+00:00
-- url     : https://prove2.me/submissions/2e744db7-8d47-40ea-a1f3-416e27afd8be

import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

theorem solution
    (Cash Error : ℝ≥0∞) (Budget : ℝ)
    (hBudgetNonneg : 0 ≤ Budget)
    (hErrorFinite : Error ≠ ⊤)
    (hCash : Cash ≤ ENNReal.ofReal Budget + Error) :
    Cash.toReal ≤ Budget + Error.toReal := by
  have hRhsFinite : ENNReal.ofReal Budget + Error ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hErrorFinite⟩
  have h := ENNReal.toReal_mono hRhsFinite hCash
  simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hErrorFinite,
    ENNReal.toReal_ofReal hBudgetNonneg] using h
