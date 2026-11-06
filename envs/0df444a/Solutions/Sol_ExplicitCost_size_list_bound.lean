-- Prove2me | solution 1 for ExplicitCost.size_list_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:09:40.687001+00:00
-- url     : https://prove2.me/submissions/1d697dfb-3e86-4f7c-9bfc-de2607716a1f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_list
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.size_list



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  have h := List.sum_le_card_nsmul (l.map fun x => size x + 1) (s + 1) fun v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    exact Nat.succ_le_succ (hs x hx)
  rw [List.length_map, smul_eq_mul] at h
  exact Nat.succ_le_succ (h.trans (Nat.mul_le_mul_right _ hl))
end ExplicitCost
