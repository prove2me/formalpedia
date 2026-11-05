-- Prove2me | solution 1 for Eight.Fact.sum_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:11:09.132881+00:00
-- url     : https://prove2.me/submissions/f3010ad3-a875-4dcd-8ede-9f9fec788919

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact
namespace Eight.Fact
theorem _root_.solution (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Pieces.Bits c, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩
end Eight.Fact
