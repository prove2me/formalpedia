-- Prove2me | solution 1 for ExplicitCost.crude_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:31.55978+00:00
-- url     : https://prove2.me/submissions/2b2184de-eae4-4554-a5e7-e492bc34f992

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CrudeBounds

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (K g lam B₁ : ℕ) (hK : 3 ≤ K) (hg : 3 ≤ g) (hlam : 1 ≤ lam) : bitsOut K g (g ^ 3 * lam) B₁ ≤ g ^ 4 * lam + g ^ 2 * B₁ := by
  have hN : 2 ≤ g ^ 4 * lam := by
    have h1 : 3 ^ 4 ≤ g ^ 4 := Nat.pow_le_pow_left hg 4
    nlinarith
  unfold bitsOut
  refine Nat.add_le_add_right (Nat.div_le_of_le_mul ?_) _
  have e : g * (g ^ 3 * lam) = g ^ 4 * lam := by ring
  rw [e]
  generalize g ^ 4 * lam = N at hN ⊢
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 3 := ⟨K - 3, by omega⟩
  have h := Nat.mul_le_mul_left (k + 1) hN
  change 2 * N + (k + 2) ≤ (k + 3) * N
  nlinarith
end ExplicitCost
