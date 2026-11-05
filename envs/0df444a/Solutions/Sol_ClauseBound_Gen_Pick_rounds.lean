-- Prove2me | solution 1 for ClauseBound.Gen.Pick.rounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:59.843211+00:00
-- url     : https://prove2.me/submissions/03668b72-63e8-4c67-9f1e-2ff58edbe258

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_ClauseBound_Gen_Pick_next_state
import Theorems.Thm_ClauseBound_Gen_Pick_len_state_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Pick
theorem _root_.solution (P : PiecesF) (x₀ : ℕ) (b : U) : ∀ r ≤ b.length, ∃ l,
    (List.replicate r ()).foldl (fun st _ => cap (padOf P.m x₀ b) ([], [], [], [], []) (next b st))
      (cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ 0)) = state P x₀ l ∧
    l ≤ r ∧ (l = 0 ∨ K x₀ l ≤ b.length) ∧ (r ≤ l ∨ b.length < K x₀ (l + 1)) := by
  have hcap : ∀ l, l ≤ b.length → (l = 0 ∨ K x₀ l ≤ b.length) →
      cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ l) = state P x₀ l := by
    intro l hl h
    refine cap_eq ?_
    rw [padOf, List.length_replicate]
    refine len_state_le P x₀ _ _ l ?_ hl
    rcases h with rfl | h
    · exact Nat.le_add_left _ _
    · exact h.trans (Nat.le_add_right _ _)
  intro r
  induction r with
  | zero => intro _; exact ⟨0, hcap 0 (Nat.zero_le _) (Or.inl rfl), le_rfl, Or.inl rfl, Or.inl le_rfl⟩
  | succ r ih =>
    intro hr
    obtain ⟨l, h1, h2, h3, h4⟩ := ih (by omega)
    rw [List.replicate_succ' (n := r), List.foldl_append, h1, List.foldl_cons, List.foldl_nil, next_state]
    by_cases hK : K x₀ (l + 1) ≤ b.length
    · rw [if_pos hK]
      exact ⟨l + 1, hcap _ (by omega) (Or.inr hK), by omega, Or.inr hK, Or.inl (by omega)⟩
    · rw [if_neg hK]
      exact ⟨l, hcap _ (by omega) h3, by omega, h3, Or.inr (by omega)⟩
end ClauseBound.Gen.Pick
