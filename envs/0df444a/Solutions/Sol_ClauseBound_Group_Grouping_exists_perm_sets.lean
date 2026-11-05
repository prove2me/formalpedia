-- Prove2me | solution 1 for ClauseBound.Group.Grouping.exists_perm_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:58.148311+00:00
-- url     : https://prove2.me/submissions/c80efe8c-11da-4e46-9e4c-65be2d9289ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
import Theorems.Thm_ClauseBound_Group_Grouping_exists_perm_of_fiber
import Theorems.Thm_ClauseBound_Group_Grouping_card_colour

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
namespace ClauseBound.Group.Grouping
theorem _root_.solution {V : Type} [Fintype V] [DecidableEq V] (A A' A'' : Finset V) (h' : Disjoint A A') (h'' : Disjoint A A'') (hc : #A' = #A'') :
    ∃ p : Equiv.Perm V, (∀ x, p x ∈ A ↔ x ∈ A) ∧ ∀ x, p x ∈ A' ↔ x ∈ A'' := by
  obtain ⟨p, hp⟩ := exists_perm_of_fiber (fun x => (decide (x ∈ A), decide (x ∈ A''))) (fun x => (decide (x ∈ A), decide (x ∈ A')))
    fun y => by rw [card_colour A A'' h'', card_colour A A' h', hc]
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have := congrArg Prod.fst (hp x)
    simpa using this
  · have := congrArg Prod.snd (hp x)
    simpa using this
end ClauseBound.Group.Grouping
