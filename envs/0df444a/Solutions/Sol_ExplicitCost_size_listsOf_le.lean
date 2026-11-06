-- Prove2me | solution 1 for ExplicitCost.size_listsOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:42.367212+00:00
-- url     : https://prove2.me/submissions/95fe7d0e-64ca-4bf4-94b3-50c58bd4e75c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
import Theorems.Thm_ExplicitCost_size_list_bound
import Theorems.Thm_ExplicitCost_size_nat_of_lt
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_int
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) :
    size (listsOf D lam) ≤ ((2 * lam) ^ c * ((2 * lam) ^ c + 1 + 1) + 1) + (((2 * lam) ^ c * (2 * lam + 1 + 1) + 1) + ((2 * lam) ^ c * (2 * lam + 1 + 1) + 1)) := by
  have hcard : ((D.fam lam).I.sort).length ≤ (2 * lam) ^ c := by
    rw [Finset.length_sort]
    exact hS.is.card lam hlam
  have h1 : size ((D.fam lam).I.sort) ≤ (2 * lam) ^ c * ((2 * lam) ^ c + 1 + 1) + 1 := size_list_bound hcard fun i hi => by
    have hi' : |i| < 2 ^ (2 * lam) ^ c := hS.is.size_I lam hlam i ((Finset.mem_sort _).1 hi)
    have h2 : i.natAbs < 2 ^ (2 * lam) ^ c := by
      have : ((i.natAbs : ℕ) : ℤ) < ((2 ^ (2 * lam) ^ c : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        exact_mod_cast hi'
      exact_mod_cast this
    rw [size_int]
    exact Nat.succ_le_succ (Nat.size_le.2 h2)
  have h2 : ∀ tr, size (((D.fam lam).I.sort).map fun i => D.cap lam tr i) ≤ (2 * lam) ^ c * (2 * lam + 1 + 1) + 1 := fun tr =>
    size_list_bound (by rw [List.length_map]; exact hcard) fun v hv => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      exact (size_nat_of_lt Nat.lt_two_pow_self).trans (Nat.succ_le_succ (hS.short lam tr i))
  exact Nat.add_le_add h1 (Nat.add_le_add (h2 false) (h2 true))
end ExplicitCost
