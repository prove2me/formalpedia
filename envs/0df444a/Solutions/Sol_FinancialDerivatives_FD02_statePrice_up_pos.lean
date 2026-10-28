-- Prove2me | solution 1 for FinancialDerivatives.FD02.statePrice_up_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:08:21.275868+00:00
-- url     : https://prove2.me/submissions/0fe78620-5e8a-41f4-883d-c5b6571ae439

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) :
  0 < riskNeutralUp m / m.growth := by
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
  unfold riskNeutralUp
  exact div_pos (div_pos (by linarith) (by linarith)) m.growth_pos
