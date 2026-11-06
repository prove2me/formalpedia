-- Prove2me | solution 1 for ExplicitCost.patternsFew
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:47.719899+00:00
-- url     : https://prove2.me/submissions/9198421f-b96f-4f0a-8635-8d3694e2f8ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Expansion
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : PatternsFew := by
  intro ρ c x₀ D hS g lam B hg hlam hB
  have h4 := ClauseBound.Gen.Rate.four_nRect_le g
  refine ⟨h4, ?_⟩
  have hX : 2 * lam ≤ Xi g lam B := by
    unfold Xi
    have h1 : 4 ≤ g ^ 2 := by nlinarith
    nlinarith
  calc (#(D.fam lam).I ^ nRectG g g) ^ 4 = #(D.fam lam).I ^ (4 * nRectG g g) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((2 * lam) ^ c) ^ (4 * nRectG g g) := Nat.pow_le_pow_left (hS.is.card lam hlam) _
    _ ≤ ((2 * lam) ^ c) ^ (g ^ 4) := Nat.pow_le_pow_right (Nat.pow_pos (by omega)) h4
    _ = (2 * lam) ^ (c * g ^ 4) := by rw [← pow_mul]
    _ ≤ Xi g lam B ^ (c * g ^ 4) := Nat.pow_le_pow_left hX _
end ExplicitCost
