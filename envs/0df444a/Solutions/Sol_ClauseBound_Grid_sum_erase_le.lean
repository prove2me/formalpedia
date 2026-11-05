-- Prove2me | solution 1 for ClauseBound.Grid.sum_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:10.66321+00:00
-- url     : https://prove2.me/submissions/ee945f1c-fc99-42ec-afe9-23de8d38fe73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_sum_le_card_mul

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {p c : ℕ} (X : Type) [Fintype X] [DecidableEq X] (hX : Fintype.card X = p) (F : X → ℕ)
    (hF : ∀ b, F b ≤ c) (a : X) : ∑ b ∈ univ.erase a, F b ≤ p * c := by
  refine (sum_le_card_mul _ _ _ fun b _ => hF b).trans ?_
  rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, hX]
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
end ClauseBound.Grid
