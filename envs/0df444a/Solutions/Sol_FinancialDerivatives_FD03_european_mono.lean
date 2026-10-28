-- Prove2me | solution 1 for FinancialDerivatives.FD03.european_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:05:07.646409+00:00
-- url     : https://prove2.me/submissions/036c22f6-7eb5-4c22-8b21-460638834fb7

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeLe
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03

theorem S200F_mono (m : BinomialMarket)
    (u₁ u₂ d₁ d₂ : ℝ) (hu : u₁ ≤ u₂) (hd : d₁ ≤ d₂) :
    oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
  unfold oneStepValue
  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  have h3 := m.down_pos
  have hp : 0 < upWeight m := by unfold upWeight; apply div_pos <;> linarith
  have hq : upWeight m < 1 := by unfold upWeight; rw [div_lt_one (by linarith)]; linarith
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (x y : PayoffTree n) (hxy : payoffTreeLe n x y) :
    europeanValue m n x ≤ europeanValue m n y := by


  induction x with
  | leaf c =>
    cases y with
    | leaf c' => exact hxy
  | branch xu xd ihu ihd =>
    cases y with
    | branch yu yd =>
      exact S200F_mono m _ _ _ _ (ihu yu hxy.1) (ihd yd hxy.2)
