-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.mem_gridCl_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:20.05242+00:00
-- url     : https://prove2.me/submissions/3829b171-21bf-489d-a57d-3225e251eb3b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridCl_D
import Theorems.Thm_Groundwork_Grid_tri_bijOn
import Theorems.Thm_Groundwork_Grid_vC_full
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_chunkAt
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    {θ : List Bool} (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    θ ∈ (gridCl P pad p d tr h ℓ y R a b).D := by
  have hdrop : (θ.drop (nMemb p d tr * ℓ)).length = ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ := by
    rw [List.length_drop, hθ]; omega
  rw [gridCl_D R hab]
  change θ ∈ (words _).filter _
  rw [mem_filter, mem_words, vC_full, mem_words]
  refine ⟨hθ, by rw [List.length_take, hθ]; omega, mem_filter.2 ⟨mem_words.2 hdrop, fun k hk => mem_words.2 ?_⟩⟩
  exact length_chunkAt _ (mem_range.1 ((tri_bijOn (nMemb p d tr)).mapsTo hk)) hdrop
end ClauseBound.Alg.GridPresents
