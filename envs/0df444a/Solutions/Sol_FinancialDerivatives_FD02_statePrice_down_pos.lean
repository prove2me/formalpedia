-- Prove2me | solution 1 for FinancialDerivatives.FD02.statePrice_down_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:08:52.422755+00:00
-- url     : https://prove2.me/submissions/c2a4a36f-d05c-43c7-9da8-1435fc9ef774

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) :
  0 < (1 - riskNeutralUp m) / m.growth := by
  have hs := m.spot_pos
  have hdu := m.down_lt_up
  have hd : m.down < m.growth := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, -⟩ := hNA ⟨1, -m.spot⟩ (by simp [initialCost])
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h1
    nlinarith
  have hu : m.growth < m.up := by
    by_contra hc
    push_neg at hc
    obtain ⟨-, h2⟩ := hNA ⟨-1, m.spot⟩ (by simp [initialCost])
      (by simp only [terminalPayoff]; nlinarith) (by simp only [terminalPayoff]; nlinarith)
    simp only [terminalPayoff] at h2
    nlinarith
  have h1 : riskNeutralUp m < 1 := by
    unfold riskNeutralUp; rw [div_lt_one (by linarith)]; linarith
  exact div_pos (by linarith) m.growth_pos
