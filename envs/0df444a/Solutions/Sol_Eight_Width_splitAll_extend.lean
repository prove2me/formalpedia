-- Prove2me | solution 1 for Eight.Width.splitAll_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:01:58.90129+00:00
-- url     : https://prove2.me/submissions/3281c804-2698-447e-8155-40576d5dcbc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_nil
import Theorems.Thm_Eight_Width_holds_cons
import Theorems.Thm_Eight_Width_holds_append
import Theorems.Thm_Eight_Width_holds_congr
import Theorems.Thm_Eight_Width_splitClause_vars
import Theorems.Thm_Eight_Width_splitClause_extend
import Theorems.Thm_Eight_Width_splitAll_cons

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution : ∀ (φ : List (List (V × Bool))) (ys : List V) (a : V → Bool), ys.Nodup →
    (∀ C ∈ φ, ∀ l ∈ C, l.1 ∉ ys) → Holds a φ → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitAll ys φ)
  | [], _, a, _, _, _ => ⟨a, fun _ _ => rfl, holds_nil a⟩
  | C :: φ, ys, a, hn, hf, h => by
    obtain ⟨hC, hφ⟩ := holds_cons.1 h
    have hsub : (ys.take (C.length - 3)).Sublist ys := List.take_sublist _ _
    have hsub' : (ys.drop (C.length - 3)).Sublist ys := List.drop_sublist _ _
    obtain ⟨b₁, hb₁, hH₁⟩ := splitClause_extend (ys.take (C.length - 3)) C a (hn.sublist hsub)
      (fun l hl hm => hf C (by simp) l hl (hsub.subset hm)) hC
    have hφ₁ : Holds b₁ φ := (holds_congr fun D hD l hl =>
      hb₁ l.1 fun hm => hf D (List.mem_cons_of_mem _ hD) l hl (hsub.subset hm)).2 hφ
    obtain ⟨b₂, hb₂, hH₂⟩ := solution φ (ys.drop (C.length - 3)) b₁ (hn.sublist hsub')
      (fun D hD l hl hm => hf D (List.mem_cons_of_mem _ hD) l hl (hsub'.subset hm)) hφ₁
    refine ⟨b₂, fun v hv => ?_, ?_⟩
    · rw [hb₂ v fun hm => hv (hsub'.subset hm), hb₁ v fun hm => hv (hsub.subset hm)]
    · rw [splitAll_cons, holds_append]
      refine ⟨(holds_congr fun D hD l hl => hb₂ l.1 fun hm => ?_).2 hH₁, hH₂⟩
      rcases splitClause_vars _ C D hD l hl with h1 | ⟨l', hl', e⟩
      · exact List.disjoint_take_drop hn le_rfl h1 hm
      · exact hf C (by simp) l' hl' (e ▸ hsub'.subset hm)
end Eight.Width
