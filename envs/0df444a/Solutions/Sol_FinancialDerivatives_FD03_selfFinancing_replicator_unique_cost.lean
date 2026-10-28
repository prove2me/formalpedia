-- Prove2me | solution 1 for FinancialDerivatives.FD03.selfFinancing_replicator_unique_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:04:11.138253+00:00
-- url     : https://prove2.me/submissions/f5b8edde-881b-4969-a398-c279c01ac9b6

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeTerminalPays
import Mathlib.Tactic
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

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (hedge : HedgeTree n)
    (hsf : SelfFinancing m n spot hedge)
    (hrep : hedgeTerminalPays n hedge claim) :
    hedgeWealth m n spot hedge = europeanValue m n claim := by


  induction claim generalizing spot with
  | leaf c =>
    cases hedge with
    | terminal cash => exact hrep
  | branch up down ihu ihd =>
    cases hedge with
    | node shares bank hu hd =>
      obtain ⟨e1, e2, s1, s2⟩ := hsf
      obtain ⟨r1, r2⟩ := hrep
      have iu := ihu (spot * m.up) (mul_pos hspot (by linarith [m.down_pos, m.down_lt_growth, m.growth_lt_up])) hu s1 r1
      have id := ihd (spot * m.down) (mul_pos hspot m.down_pos) hd s2 r2
      show shares * spot + bank = oneStepValue m _ _
      exact S200F_cost m spot shares bank _ _ (e1.trans iu) (e2.trans id)
