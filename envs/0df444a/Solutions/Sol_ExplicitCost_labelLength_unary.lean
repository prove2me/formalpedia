-- Prove2me | solution 1 for ExplicitCost.labelLength_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:12:54.610222+00:00
-- url     : https://prove2.me/submissions/47cc3ffc-6927-4af3-a41a-0b7ba32ab940

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_Poly
import Definitions.Def_Exits_Poly
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_PaddedDescent_F_CertNet
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingPoly
import Theorems.Thm_ExplicitCost_inG_unary
import Theorems.Thm_ExplicitCost_inP_unary
import Theorems.Thm_ExplicitCost_inU_unary
import Theorems.Thm_ExplicitCost_labelLength_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_le
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul


section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet
variable {α : Type} [Enc α]
private theorem label_le (a b K g P U : ℕ) : (b * U + 2 * min a b * g * P + b * K ^ 2 - 1) / (b * K ^ 2) ≤ U + 2 * g * P + 1 := by
  obtain ⟨d, hd⟩ : ∃ d, d = b * K ^ 2 := ⟨_, rfl⟩
  rw [← hd]
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0, Nat.div_zero]
    omega
  · have hK : 0 < K ^ 2 := Nat.pos_of_mul_pos_left (hd ▸ hpos)
    have hbd : b ≤ d := hd ▸ Nat.le_mul_of_pos_right _ hK
    have n1 : b * U ≤ d * U := Nat.mul_le_mul_right _ hbd
    have n2 : 2 * min a b * g * P ≤ d * (2 * g * P) :=
      calc 2 * min a b * g * P = min a b * (2 * g * P) := by ring
        _ ≤ d * (2 * g * P) := Nat.mul_le_mul_right _ ((min_le_right a b).trans hbd)
    have e : d * (U + 2 * g * P + 1) = d * U + d * (2 * g * P) + d := by ring
    apply Nat.div_le_of_le_mul
    rw [e]
    omega
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet
variable {α : Type} [Enc α]
namespace ExplicitCost
theorem _root_.solution {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => labelLength (c t) :=
  Unary.of_le (g := fun t => inU (c t) + 2 * inG (c t) * inP (c t) + 1)
    (((inU_unary hc).add (((Unary.const 2).mul (inG_unary hc)).mul (inP_unary hc))).add (Unary.const 1)) (labelLength_polyT hc) fun _ => label_le _ _ _ _ _ _
end ExplicitCost
