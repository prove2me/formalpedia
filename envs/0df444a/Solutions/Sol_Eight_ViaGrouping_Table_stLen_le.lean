-- Prove2me | solution 1 for Eight.ViaGrouping.Table.stLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:14.838201+00:00
-- url     : https://prove2.me/submissions/7944f927-c395-4ff0-8b4f-16fc92fc227c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_mem_members
import Theorems.Thm_Eight_ViaGrouping_Table_sum_map_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_NetE_sum_map_le
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) {x G m : ℕ} (hm : (members K g x G).length ≤ m) : stLen K g Np.toPaperNetwork c x G ≤ P * m := by
  unfold stLen stLens
  refine (sum_map_le _ _ P fun a ha => ?_).trans ?_
  · have hag := (mem_members.1 ha).1
    change Np.len c a ≤ P
    rw [h.given.len_eq ⟨a, hag⟩]
    exact h.is.len_le _
  · rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hm
end Eight.ViaGrouping.Table
