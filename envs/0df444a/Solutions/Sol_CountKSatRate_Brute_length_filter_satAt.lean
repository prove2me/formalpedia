-- Prove2me | solution 1 for CountKSatRate.Brute.length_filter_satAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:35.125046+00:00
-- url     : https://prove2.me/submissions/bc50bba3-29f2-4c1a-910e-3fe2a50861a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Batteries.Data.Nat.Lemmas
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_CountKSatRate_Brute
import Theorems.Thm_CountKSatRate_Brute_satAt_toN
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.testBit



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)
namespace CountKSatRate.Brute
theorem _root_.solution {n : ℕ} (φ : CNF n) : ((List.range (2 ^ n)).filter fun y => satAt (toN φ) y).length = numSat φ := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), numSat]
  refine Finset.card_bij' (fun y _ => fun i : Fin n => y.testBit i) (fun a _ => Nat.ofBits a) ?_ ?_ ?_ ?_
  · intro y hy
    have h := (List.mem_filter.1 (List.mem_toFinset.1 hy)).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (satAt_toN φ y).1 h⟩
  · intro a ha
    refine List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (Nat.ofBits_lt_two_pow a), (satAt_toN φ _).2 fun C hC => ?_⟩)
    obtain ⟨l, hl, h⟩ := (Finset.mem_filter.1 ha).2 C hC
    exact ⟨l, hl, by rw [Nat.testBit_ofBits_lt a _ l.1.2]; exact h⟩
  · intro y hy
    have h := List.mem_range.1 (List.mem_filter.1 (List.mem_toFinset.1 hy)).1
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt h]
  · intro a _
    funext i
    exact Nat.testBit_ofBits_lt a _ i.2
end CountKSatRate.Brute
