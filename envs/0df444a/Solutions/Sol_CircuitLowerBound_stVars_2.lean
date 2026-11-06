-- Prove2me | solution 2 for CircuitLowerBound.stVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:54.048436+00:00
-- url     : https://prove2.me/submissions/40a8b08d-bda5-4241-bf4a-a58e90a2d88a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_pack_lt
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts
namespace CircuitLowerBound
theorem _root_.solution : StVars := by
  intro e L P hF C hC l hl
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hC
  have hlt : ∀ l' : TLit, vidx e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) l' < 2 ^ L := by
    intro l'
    have ht : j / 2 ^ bq e L % 2 ^ bt e L < 2 ^ bt e L := Nat.mod_lt _ (by positivity)
    have h1 : l'.1 % 2 ^ kb e < 2 ^ kb e := Nat.mod_lt _ (by positivity)
    have h2 : tval (bt e L) (j / 2 ^ bq e L % 2 ^ bt e L) l'.2.1 < 2 ^ (bt e L + 1) := by
      rw [pow_succ]
      unfold tval
      split_ifs <;> omega
    have h3 : (qval P (j % 2 ^ bq e L) l'.2.2.1 + l'.2.2.2.1) % 2 ^ (bq e L + 1) < 2 ^ (bq e L + 1) := Nat.mod_lt _ (by positivity)
    have h5 : vidx e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) l' < 2 ^ kb e * 2 ^ (bt e L + 1) * 2 ^ (bq e L + 1) :=
      pack_lt (pack_lt h1 h2) h3
    refine lt_of_lt_of_le h5 ?_
    rw [← pow_add, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := hF.1
    unfold bq bt
    omega
  simp only [clauseAt, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> exact hlt _
end CircuitLowerBound
