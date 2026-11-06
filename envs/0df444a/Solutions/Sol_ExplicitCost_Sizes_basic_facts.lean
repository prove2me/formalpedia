-- Prove2me | solution 1 for ExplicitCost.Sizes.basic_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:07:16.819603+00:00
-- url     : https://prove2.me/submissions/cae547e8-c99c-4ebc-ac6d-f9027c24e856

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes
namespace ExplicitCost.Sizes
theorem _root_.solution {g P B : ℕ} (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) :
    2 * g ≤ g * (P + B) ∧ P + B ≤ g * (P + B) ∧ g * g ≤ g * g * (P + B) ∧ g * g * P ≤ g * g * (P + B) ∧ B * (g * g) ≤ g * g * (P + B) ∧
      g * g * (P + B) ≤ g * (P + B) * (g * (P + B)) ∧ 2 * (g * (P + B)) ≤ g * (P + B) * (g * (P + B)) := by
  have h1 : 2 * g ≤ g * (P + B) := by
    rw [Nat.mul_comm 2 g]
    exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨h1, Nat.le_mul_of_pos_left _ hg, Nat.le_mul_of_pos_right _ (by omega), Nat.mul_le_mul_left _ (by omega), ?_, ?_, Nat.mul_le_mul_right _ (by omega)⟩
  · rw [Nat.mul_comm B]
    exact Nat.mul_le_mul_left _ (by omega)
  · calc g * g * (P + B) = g * g * (P + B) * 1 := (Nat.mul_one _).symm
      _ ≤ g * g * (P + B) * (P + B) := Nat.mul_le_mul_left _ (by omega)
      _ = g * (P + B) * (g * (P + B)) := by ring
end ExplicitCost.Sizes
