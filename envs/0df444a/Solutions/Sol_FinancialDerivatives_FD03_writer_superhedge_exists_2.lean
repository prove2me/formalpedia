-- Prove2me | solution 2 for FinancialDerivatives.FD03.writer_superhedge_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:17.313268+00:00
-- url     : https://prove2.me/submissions/97bb1b76-f0d4-42fb-9ea4-44425b1b6e68

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_snellValue
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
import Definitions.Def_fd03_localHedge
open FinancialDerivatives.FD03

theorem S200F_cost (m : BinomialMarket) (s α β vu vd : ℝ)
    (hu : α * (s * m.up) + β * m.growth = vu) (hd : α * (s * m.down) + β * m.growth = vd) :
    α * s + β = oneStepValue m vu vd := by
  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  have h3 := m.down_pos
  have hud : m.up - m.down ≠ 0 := by linarith
  have hg : m.growth ≠ 0 := by linarith
  unfold oneStepValue upWeight
  subst hu hd
  field_simp
  ring

theorem S200F_G (m : BinomialMarket) (n : ℕ) :
    ∀ (spot capital : ℝ), 0 < spot → ∀ (exercise : ExerciseTree n),
    snellValue m n exercise ≤ capital →
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = capital := by
  induction n with
  | zero =>
    intro spot capital _ exercise hc
    cases exercise with
    | maturity r => exact ⟨.terminal capital, trivial, hc, rfl⟩
  | succ n ih =>
    intro spot capital hspot exercise hc
    cases exercise with
    | node allowed reward U D =>
      have h1 := m.down_lt_growth
      have h2 := m.growth_lt_up
      have h3 := m.down_pos
      have hud : m.up - m.down ≠ 0 := by linarith
      have hg : m.growth ≠ 0 := by linarith
      have hs : spot ≠ 0 := hspot.ne'
      set vU := snellValue m n U
      set vD := snellValue m n D
      set C := oneStepValue m vU vD
      have hCs : C ≤ snellValue m (n + 1) (.node allowed reward U D) := by
        cases allowed
        · exact le_rfl
        · exact le_max_right _ _
      have hRs : allowed = true → reward ≤ snellValue m (n + 1) (.node allowed reward U D) := by
        intro h; subst h; exact le_max_left _ _
      set e := capital - C
      have he : 0 ≤ e := by simp only [e]; linarith
      have hgp : 0 < m.growth := by linarith
      obtain ⟨hU, sU, cU, wU⟩ := ih (spot * m.up) (vU + e * m.growth) (mul_pos hspot (by linarith)) U
        (by nlinarith)
      obtain ⟨hD, sD, cD, wD⟩ := ih (spot * m.down) (vD + e * m.growth) (mul_pos hspot h3) D
        (by nlinarith)
      set α := (localHedge m spot vU vD).1
      set β := (localHedge m spot vU vD).2
      have eU : α * (spot * m.up) + β * m.growth = vU := by
        simp only [α, β]; unfold localHedge; simp only; field_simp; ring
      have eD : α * (spot * m.down) + β * m.growth = vD := by
        simp only [α, β]; unfold localHedge; simp only; field_simp; ring
      have hcost := S200F_cost m spot α β vU vD eU eD
      refine ⟨.node α (β + e) hU hD, ⟨?_, ?_, sU, sD⟩, ⟨?_, cU, cD⟩, ?_⟩
      · rw [wU]; linarith
      · rw [wD]; linarith
      · intro h; have := hRs h; linarith
      · show α * spot + (β + e) = capital
        simp only [e] at *; linarith

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = snellValue m n exercise := by


  exact S200F_G m n spot _ hspot exercise le_rfl
