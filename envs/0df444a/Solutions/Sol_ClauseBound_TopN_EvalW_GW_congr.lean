-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.GW_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:25.842441+00:00
-- url     : https://prove2.me/submissions/841819ba-1bd5-417a-a23e-f8052356d0a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution (R : ℕ) (ws : List ℤ) (lo hi : List ℕ) (t t' : ℕ → ℕ) (h : ∀ i < R, t i = t' i) : GW R ws lo hi t = GW R ws lo hi t' := by
  unfold GW
  refine prod_congr rfl fun i hi' => ?_
  rw [h i (mem_range.1 hi')]
end ClauseBound.TopN.EvalW
