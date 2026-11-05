-- Prove2me | solution 1 for ClauseBound.Grid.sum_erase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:24.684421+00:00
-- url     : https://prove2.me/submissions/b97acb0a-b64a-4ed8-9910-074a3a1c5f30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {X : Type} [Fintype X] [LinearOrder X] (h : X × X → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) = 2 * ∑ q ∈ pairs X, h q := by
  have h0 : ∀ a b : X, (if b ≠ a then h (min a b, max a b) else 0) =
      (if a < b then h (a, b) else 0) + (if b < a then h (b, a) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne', hab.le, not_lt.2 hab.le]
    · simp [hab]
    · simp [hab, hab.ne, hab.le, not_lt.2 hab.le]
  have h1 : ∑ q ∈ pairs X, h q = ∑ a, ∑ b, if a < b then h (a, b) else 0 := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ a : X, ∑ b : X, (if b < a then h (b, a) else 0) = ∑ a, ∑ b, if a < b then h (a, b) else 0 :=
    Finset.sum_comm
  calc ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b)
      = ∑ a, ∑ b, if b ≠ a then h (min a b, max a b) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.filter_ne' univ a, Finset.sum_filter]
    _ = 2 * ∑ q ∈ pairs X, h q := by
        simp only [h0, Finset.sum_add_distrib]
        rw [h2, h1, two_mul]
end ClauseBound.Grid
