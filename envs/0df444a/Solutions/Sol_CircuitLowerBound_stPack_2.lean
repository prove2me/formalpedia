-- Prove2me | solution 2 for CircuitLowerBound.stPack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:08.531186+00:00
-- url     : https://prove2.me/submissions/d48b6dc5-840c-4ae0-b640-1014782d6368

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack
import Theorems.Thm_CircuitLowerBound_Pack_div_pack
import Theorems.Thm_CircuitLowerBound_Pack_mod_pack
import Theorems.Thm_CircuitLowerBound_Pack_vidx_eq
import Theorems.Thm_CircuitLowerBound_Pack_clauseAt_pack
import Theorems.Thm_CircuitLowerBound_Pack_exists_pack
import Theorems.Thm_CircuitLowerBound_Pack_pack_lt
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open Pack
namespace CircuitLowerBound
theorem _root_.solution : StPack := by
  intro e L P hg hF
  have hsat : Sat (tabF e L P) ↔ ∃ a : ℕ → Bool, ∀ j < 2 ^ nb e L, ∃ l ∈ clauseAt e L P j, a l.1 = l.2 := by
    unfold Sat tabF
    simp only [List.forall_mem_map, List.mem_range]
  rw [hsat]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun k t q => a ((k * 2 ^ (bt e L + 1) + t) * 2 ^ (bq e L + 1) + q), fun c hc t ht q hq => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨l', hl', hal⟩ := ha _ (pack_lt (hr.trans (Nat.lt_size_self _)) ht hq)
    rw [clauseAt_pack e L P ht hq, List.getD_eq_getElem _ _ hr] at hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    refine ⟨l, hl, ?_⟩
    rw [litAt, (vidx_eq hg hF hc hl ht hq).1] at hal
    exact hal
  · rintro ⟨α, hα⟩
    refine ⟨fun v => if v / 2 ^ (bq e L + 1) / 2 ^ (bt e L + 1) = 0 then false
      else α (v / 2 ^ (bq e L + 1) / 2 ^ (bt e L + 1)) (v / 2 ^ (bq e L + 1) % 2 ^ (bt e L + 1)) (v % 2 ^ (bq e L + 1)), fun j _ => ?_⟩
    obtain ⟨r, t, q, ht, hq, rfl⟩ := exists_pack e L j
    rw [clauseAt_pack e L P ht hq]
    by_cases hr : r < (tab e).length
    · rw [List.getD_eq_getElem _ _ hr]
      have hc := List.getElem_mem hr
      obtain ⟨l, hl, hh⟩ := hα _ hc t ht q hq
      refine ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
      obtain ⟨h1, h2, h3⟩ := vidx_eq hg hF hc hl ht hq
      have hk := (hg _ hc l hl).1
      simp only [litAt, h1, div_pack h3, mod_pack h3, div_pack h2, mod_pack h2]
      rw [if_neg (by omega)]
      exact hh
    · rw [List.getD_eq_default _ _ (by omega)]
      refine ⟨_, List.mem_map.2 ⟨zeroCl.1, by simp [lits], rfl⟩, ?_⟩
      have : vidx e L P t q zeroCl.1 = 0 := by simp [vidx, zeroCl, tval, qval]
      simp only [litAt, this]
      simp [zeroCl]
end CircuitLowerBound
