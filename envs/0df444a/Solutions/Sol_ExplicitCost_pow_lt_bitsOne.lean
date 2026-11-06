-- Prove2me | solution 1 for ExplicitCost.pow_lt_bitsOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:41:51.076502+00:00
-- url     : https://prove2.me/submissions/8804c0cf-7c59-4cf3-bdb6-187e8cd7f730

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hg : 1 ≤ g) (hB : 1 ≤ B) : (2 : ℤ) ^ (nMemb g g tr * 0 + nMemb g g tr ^ 2 * (2 * lam) ^ c) < 2 ^ bitsOne c g lam B := by
  refine pow_lt_pow_right₀ (by norm_num) ?_
  rw [nMemb_self]
  unfold bitsOne
  have : 1 ≤ g * B := Nat.mul_pos hg hB
  omega
end ExplicitCost
