-- Prove2me | solution 1 for CountKSat.cntN_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:27:49.044311+00:00
-- url     : https://prove2.me/submissions/ea51ca36-5839-4974-85c9-b8066a681f1d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Definitions.Def_CountKSat_StepCount
import Theorems.Thm_CountKSat_StepCount_holds_append
import Theorems.Thm_CountKSat_StepCount_holds_addP
import Theorems.Thm_CountKSat_StepCount_holds_singleton
import Theorems.Thm_CountKSat_StepCount_holds_negU
import Theorems.Thm_CountKSat_StepCount_holds_petals
import Theorems.Thm_CountKSat_StepCount_card_split
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open StepCount
namespace CountKSat
theorem _root_.solution (n : ℕ) (X s : PFml) (H : PCl) (P : PFml) (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q) :
    cntN n (X ++ s) = cntN n (X ++ addP [H] s) + cntN n ((negU H ++ X) ++ addP P s) := by
  refine card_split _ (fun a : Fin n → Bool => ∃ l ∈ H, ext a l.1 = l.2) _ _ (fun a => ?_) (fun a => ?_)
  · change Holds _ _ ↔ Holds _ _ ∧ _
    rw [holds_append, holds_append, holds_addP, holds_singleton]
    tauto
  · change Holds _ _ ↔ Holds _ _ ∧ _
    rw [holds_append, holds_append, holds_append, holds_addP, holds_negU]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h4⟩; exact ⟨⟨h2, h4⟩, h1⟩
    · rintro ⟨⟨h2, h4⟩, h1⟩; exact ⟨⟨h1, h2⟩, holds_petals hP h1 h4, h4⟩
end CountKSat
