-- Prove2me | solution 1 for ClauseBound.Inst.Half.lookT_tab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:06.067279+00:00
-- url     : https://prove2.me/submissions/4eb18605-d2c5-419f-90b7-193f1a3d1b77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Half_getD_flatMap_map

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {flat : List (List ℕ)} (f : List ℕ → List ℕ → ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    lookT flat (tab flat f) π σ = f π σ := by
  have h1 := List.idxOf_lt_length_iff.2 hπ
  have h2 := List.idxOf_lt_length_iff.2 hσ
  rw [lookT, tab, getD_flatMap_map flat f flat _ _ h1 h2, List.getElem_idxOf h1, List.getElem_idxOf h2]
end ClauseBound.Inst.Half
