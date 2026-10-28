-- Prove2me | solution 1 for FinancialDerivatives.FD03.recursiveHedge_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:04:17.434751+00:00
-- url     : https://prove2.me/submissions/7063ec3d-4462-4c70-b5bb-ab1bbf4286ba

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeTerminalPays
import Definitions.Def_fd03_localHedge
import Mathlib.Tactic
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

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (spot : ℝ) (hspot : 0 < spot) (claim : PayoffTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeTerminalPays n hedge claim ∧
      hedgeWealth m n spot hedge = europeanValue m n claim := by


  induction claim generalizing spot with
  | leaf c => exact ⟨.terminal c, trivial, rfl, rfl⟩
  | branch up down ihu ihd =>
    have hup : 0 < spot * m.up := mul_pos hspot (by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up])
    obtain ⟨hU, sU, pU, wU⟩ := ihu (spot * m.up) hup
    obtain ⟨hD, sD, pD, wD⟩ := ihd (spot * m.down) (mul_pos hspot m.down_pos)
    set vu := europeanValue m _ up
    set vd := europeanValue m _ down
    have h1 := m.down_lt_growth
    have h2 := m.growth_lt_up
    have h3 := m.down_pos
    have hud : m.up - m.down ≠ 0 := by linarith
    have hg : m.growth ≠ 0 := by linarith
    have hs : spot ≠ 0 := hspot.ne'
    have eU : (localHedge m spot vu vd).1 * (spot * m.up) + (localHedge m spot vu vd).2 * m.growth = vu := by
      unfold localHedge; simp only; field_simp; ring
    have eD : (localHedge m spot vu vd).1 * (spot * m.down) + (localHedge m spot vu vd).2 * m.growth = vd := by
      unfold localHedge; simp only; field_simp; ring
    refine ⟨.node (localHedge m spot vu vd).1 (localHedge m spot vu vd).2 hU hD,
      ⟨eU.trans wU.symm, eD.trans wD.symm, sU, sD⟩, ⟨pU, pD⟩, ?_⟩
    show (localHedge m spot vu vd).1 * spot + (localHedge m spot vu vd).2 = oneStepValue m vu vd
    exact S200F_cost m spot _ _ vu vd eU eD
