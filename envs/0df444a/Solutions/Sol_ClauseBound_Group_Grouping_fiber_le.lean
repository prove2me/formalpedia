-- Prove2me | solution 1 for ClauseBound.Group.Grouping.fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:41.228039+00:00
-- url     : https://prove2.me/submissions/3a9d4243-de71-4692-9f47-c2639544c673

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
import Theorems.Thm_ClauseBound_Group_Grouping_mem_cls_mul

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace ClauseBound.Group.Grouping
theorem _root_.solution (Ω' : Finset (Equiv.Perm (Fin (K * n)))) (p : Equiv.Perm (Fin (K * n))) (hΩ : ∀ e ∈ Ω', e * p ∈ Ω') (γ' : Fin K)
    (A' A'' : Finset (Fin (K * n))) (hp : ∀ x, p x ∈ A' ↔ x ∈ A'') : #{e ∈ Ω' | cls e γ' = A'} ≤ #{e ∈ Ω' | cls e γ' = A''} := by
  refine card_le_card_of_injOn (fun e => e * p) (fun e he => ?_) fun e _ e' _ h => mul_right_cancel h
  obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 he)
  refine mem_coe.2 (mem_filter.2 ⟨hΩ e h1, ?_⟩)
  ext a
  rw [mem_cls_mul, h2, hp]
end ClauseBound.Group.Grouping
