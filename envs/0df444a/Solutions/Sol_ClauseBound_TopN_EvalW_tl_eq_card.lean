-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.tl_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:06.536538+00:00
-- url     : https://prove2.me/submissions/9f9c95ba-f7c1-4de0-8494-0f3be941f572

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_oc
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution {k g n : ℕ} {Ls : List Fml} {y : ℕ} {P : Finset ℕ} (hg : 0 < g) (hW : WfL k n Ls) (hP : P ⊆ range (cls Ls).length)
    (hM : Match g n Ls y P) {i : ℕ} (hi : i < Ls.length) : tl g Ls y i = (layP Ls P i).card := by
  rw [tl, Prof.sum_map_range, ← Prof.sum_oc hg hW hP i]
  exact Finset.sum_congr rfl fun a ha => ((hM i hi a (mem_range.1 ha)).1).symm
end ClauseBound.TopN.EvalW
