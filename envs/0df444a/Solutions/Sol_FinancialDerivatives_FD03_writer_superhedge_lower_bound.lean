-- Prove2me | solution 1 for FinancialDerivatives.FD03.writer_superhedge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:08:59.832811+00:00
-- url     : https://prove2.me/submissions/4eb35a33-d3b6-4e3a-8df3-eeb0efa298c3

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) (hedge : HedgeTree n)
    (hsf : SelfFinancing m n spot hedge)
    (hcover : hedgeCoversExercise m n spot hedge exercise) :
    snellValue m n exercise ≤ hedgeWealth m n spot hedge := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  have mono : ∀ u₁ u₂ d₁ d₂ : ℝ, u₁ ≤ u₂ → d₁ ≤ d₂ → oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
    intro u₁ u₂ d₁ d₂ hu hd
    unfold oneStepValue
    have h0 : 0 < upWeight m := by
      unfold upWeight
      exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
    have h1 : upWeight m < 1 := by
      unfold upWeight
      rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
      linarith [m.growth_lt_up]
    have hg : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
    apply div_le_div_of_nonneg_right _ hg.le
    nlinarith
  induction hedge generalizing spot with
  | terminal cash => cases exercise; exact hcover
  | node sh b uH dH ihu ihd =>
    cases exercise with
    | node a r uE dE =>
      obtain ⟨h1, h2, h3, h4⟩ := hsf
      obtain ⟨c0, c1, c2⟩ := hcover
      have key : oneStepValue m (snellValue m _ uE) (snellValue m _ dE) ≤ sh * spot + b := by
        have e : sh * spot + b = oneStepValue m (hedgeWealth m _ (spot * m.up) uH)
            (hedgeWealth m _ (spot * m.down) dH) := by
          rw [← h1, ← h2]
          unfold oneStepValue upWeight
          field_simp
          ring
        rw [e]
        exact mono _ _ _ _ (ihu _ (mul_pos hspot hupos) _ h3 c1) (ihd _ (mul_pos hspot m.down_pos) _ h4 c2)
      show _ ≤ sh * spot + b
      cases a
      · exact key
      · exact max_le (c0 rfl) key


