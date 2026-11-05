-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.card_putIn_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:43.569695+00:00
-- url     : https://prove2.me/submissions/092ba123-3631-42a9-bd8d-d579b7d05698

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (Λ : ℕ → Finset (Fin q.m)) (j : ℕ) (x : Fin q.m) (j' : ℕ) : #(putIn j Λ x j') ≤ #(Λ j') + if j' = j then 1 else 0 := by
  unfold putIn
  by_cases h : j' = j
  · rw [h, Function.update_self, if_pos rfl]
    exact card_insert_le _ _
  · rw [Function.update_of_ne h, if_neg h]
    exact le_rfl
end ClauseBound.ParityChecks.Run
