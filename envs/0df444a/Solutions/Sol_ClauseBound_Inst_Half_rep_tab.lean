-- Prove2me | solution 1 for ClauseBound.Inst.Half.rep_tab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:26.079678+00:00
-- url     : https://prove2.me/submissions/90b98a96-46bd-4f4f-86b2-0543684c7114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Half_lookT_tab
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {F : ℤ → Ker}
    (h : ∀ π ∈ flat, ∀ σ ∈ flat, f π σ = F ((π.sum : ℤ) - σ.sum) π σ) : Rep flat (tab flat f) F :=
  fun π hπ σ hσ => (lookT_tab f hπ hσ).trans (h π hπ σ hσ)
end ClauseBound.Inst.Half
