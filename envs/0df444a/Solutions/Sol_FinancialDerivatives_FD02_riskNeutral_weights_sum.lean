-- Prove2me | solution 1 for FinancialDerivatives.FD02.riskNeutral_weights_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:06:43.83148+00:00
-- url     : https://prove2.me/submissions/2c2299e6-18a0-43de-a607-ed3ccf14183b

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hNA : NoArbitrage m) :
  riskNeutralUp m + (1 - riskNeutralUp m) = 1 ∧ 0 < riskNeutralUp m ∧ 0 < 1 - riskNeutralUp m := by
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
  have h0 : 0 < riskNeutralUp m := by
    unfold riskNeutralUp; exact div_pos (by linarith) (by linarith)
  have h1 : riskNeutralUp m < 1 := by
    unfold riskNeutralUp; rw [div_lt_one (by linarith)]; linarith
  exact ⟨by ring, h0, by linarith⟩
