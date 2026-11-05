-- Prove2me | solution 1 for ClauseBound.Group.Grouping.card_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:16.987253+00:00
-- url     : https://prove2.me/submissions/e178625f-0ba9-4953-80c2-9c52afed3855

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
import Theorems.Thm_ClauseBound_Group_Grouping_mem_cls

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace ClauseBound.Group.Grouping
theorem _root_.solution (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #(cls e γ) = n := by
  have h : cls e γ = (({γ} : Finset (Fin K)) ×ˢ (univ : Finset (Fin n))).map (finProdFinEquiv.trans e.symm).toEmbedding := by
    ext a
    simp only [mem_cls, chi0, mem_map, mem_product, mem_singleton, mem_univ, and_true, Equiv.coe_toEmbedding, Equiv.trans_apply]
    constructor
    · intro h
      exact ⟨finProdFinEquiv.symm (e a), h, by rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
  rw [h, card_map, card_product, card_singleton, card_univ, Fintype.card_fin, Nat.one_mul]
end ClauseBound.Group.Grouping
