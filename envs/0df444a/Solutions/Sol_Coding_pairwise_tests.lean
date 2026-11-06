-- Prove2me | solution 1 for Coding.pairwise_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:33.786302+00:00
-- url     : https://prove2.me/submissions/c836c041-67a5-46c4-9d4c-7239ef13372a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_pairwise_occIn
import Theorems.Thm_Coding_pairwise_product
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) : ((tests Φ).map fun p => (place p.1, place p.2)).Pairwise lexLt := by
  rw [List.pairwise_map]
  refine ((pairwise_product (pairwise_occIn h3 0 Φ.length) (pairwise_occIn h3 0 Φ.length)).filter _).imp ?_
  rintro p q (h | ⟨h1, h2⟩)
  · exact Or.inl h
  · exact Or.inr ⟨congrArg place h1, h2⟩
end Coding
