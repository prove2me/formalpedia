-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_lower_strip_dividend_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:00:49.058501+00:00
-- url     : https://prove2.me/submissions/693719ed-46f8-4db7-acf9-3128e958936b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
open MeasureTheory Set Filter
noncomputable section
set_option autoImplicit false

theorem solution
    (g : ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmono : MonotoneOn g (Ici 0))
    (hsec : ∀ a b : ℝ, δ ≤ a → a ≤ b →
      b - a ≤ g b - g a)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    a - b ≤ g a - g b + δ := by
  have ha : 0 ≤ a := hb.trans hba
  have hm : g b ≤ g a := hmono hb ha hba
  by_cases hbδ : δ ≤ b
  · have hs := hsec b a hbδ hba
    linarith
  · by_cases haδ : δ ≤ a
    · have hs := hsec δ a le_rfl haδ
      have hmδ : g b ≤ g δ :=
        hmono hb hδ (le_of_not_ge hbδ)
      linarith
    · have hh : a < δ := lt_of_not_ge haδ
      linarith
