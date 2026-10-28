-- Prove2me | solution 1 for FinancialDerivatives.FD03.writer_superhedge_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:06.816445+00:00
-- url     : https://prove2.me/submissions/84180bee-a57a-43e8-9191-f60e98008ccc

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_localHedge
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = snellValue m n exercise := by
  have hud : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
  have hg : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
  have hupos : 0 < m.up := by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up]
  have gen : ∀ (n : ℕ) (spot capital : ℝ), 0 < spot → ∀ (exercise : ExerciseTree n),
      snellValue m n exercise ≤ capital → ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧ hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = capital := by
    intro n spot capital hspot exercise hcapital
    induction exercise generalizing spot capital with
    | maturity r => exact ⟨.terminal capital, trivial, hcapital, rfl⟩
    | node a r uE dE ihu ihd =>
      have hs : spot ≠ 0 := hspot.ne'
      have hgp : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
      set Vu := snellValue m _ uE
      set Vd := snellValue m _ dE
      have hC : oneStepValue m Vu Vd ≤ capital := by
        refine le_trans ?_ hcapital
        cases a
        · exact le_rfl
        · exact le_max_right _ _
      have hR : a = true → r ≤ capital := by
        rintro rfl
        exact le_trans (le_max_left _ _) hcapital
      set e := capital - oneStepValue m Vu Vd with he
      have he0 : 0 ≤ e := by linarith
      obtain ⟨hu, hu1, hu2, hu3⟩ := ihu (spot * m.up) (Vu + e * m.growth) (mul_pos hspot hupos)
        (by nlinarith)
      obtain ⟨hd, hd1, hd2, hd3⟩ := ihd (spot * m.down) (Vd + e * m.growth) (mul_pos hspot m.down_pos)
        (by nlinarith)
      have hcost : (localHedge m spot Vu Vd).1 * spot + ((localHedge m spot Vu Vd).2 + e) = capital := by
        rw [he]
        unfold localHedge oneStepValue upWeight; dsimp only; field_simp; ring
      refine ⟨.node (localHedge m spot Vu Vd).1 ((localHedge m spot Vu Vd).2 + e) hu hd,
        ⟨?_, ?_, hu1, hd1⟩, ⟨fun ha => (hR ha).trans hcost.ge, hu2, hd2⟩, hcost⟩
      · rw [hu3]; unfold localHedge; dsimp only; field_simp; ring
      · rw [hd3]; unfold localHedge; dsimp only; field_simp; ring
  exact gen n spot _ hspot exercise le_rfl


