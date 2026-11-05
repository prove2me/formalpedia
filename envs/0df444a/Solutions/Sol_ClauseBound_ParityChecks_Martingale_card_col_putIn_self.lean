-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.card_col_putIn_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:23.453198+00:00
-- url     : https://prove2.me/submissions/ecda7ab6-8da3-4c18-a4b9-fc7a56979d09

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_putIn_same
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_putIn_ne
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_notMem_of_mem

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    #{j' ∈ range r | e ∈ putIn j Λ e j'} = #{j' ∈ range r | e ∈ Λ j'} + 1 := by
  have h : {j' ∈ range r | e ∈ putIn j Λ e j'} = insert j {j' ∈ range r | e ∈ Λ j'} := by
    ext j'
    by_cases hjj : j' = j
    · subst hjj
      simp [putIn_same, hS.j_lt]
    · simp [putIn_ne hjj, hjj]
  have hn : j ∉ {j' ∈ range r | e ∈ Λ j'} := fun h' => notMem_of_mem hS he (mem_filter.1 h').2
  rw [h, card_insert_of_notMem hn]
end ClauseBound.ParityChecks.Martingale
