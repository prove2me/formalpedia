-- Prove2me | solution 2 for AvramDividend.Classical.avram_chat24_initial_cash_of_global_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:23:02.31706+00:00
-- url     : https://prove2.me/submissions/b0dc52a9-68ba-4626-b1bf-0e3385301c3d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (w : ℝ → ℝ) (hm : MonotoneOn w (Ici 0)) (hn : ∀ y, 0 ≤ w y)
    (x : ℝ) (hx : 0 ≤ x) (δ : ℝ) (hδ : 0 ≤ δ) (d : ℝ)
    (hd : d ≤ w x - w (x - d)) : d ≤ w (x + δ) := by
  have hwx := hm hx (show 0 ≤ x + δ by linarith) (show x ≤ x + δ by linarith)
  have hwpost := hn (x - d)
  linarith
end
