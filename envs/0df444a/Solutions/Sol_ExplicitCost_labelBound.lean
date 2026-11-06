-- Prove2me | solution 1 for ExplicitCost.labelBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:20.066215+00:00
-- url     : https://prove2.me/submissions/096b169d-729f-4253-9256-b74fff60a372

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
import Theorems.Thm_ExplicitCost_label_first
import Theorems.Thm_GeneralPieces_Chain_inv_g_le_zeta


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : LabelBound := by
  intro ρ c x₀ l lam U _ hx _ hU
  have h1 := label_first x₀ l lam U
  have h3 : (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * (1 / Levels.Gen.g x₀ l) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * Levels.Gen.zeta l :=
    mul_le_mul_of_nonneg_left (GeneralPieces.Chain.inv_g_le_zeta x₀ l hx) (by positivity)
  linarith
end ExplicitCost
