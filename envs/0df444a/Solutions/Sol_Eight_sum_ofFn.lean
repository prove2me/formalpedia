-- Prove2me | solution 1 for Eight.sum_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:54:07.398985+00:00
-- url     : https://prove2.me/submissions/54d81dc5-0a5e-4e11-bb16-62644fe0e836

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_Eight_App_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_App_Rate
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork ClauseBound.Alg
namespace Eight
theorem _root_.solution (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Pieces.Bits c, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩
end Eight
