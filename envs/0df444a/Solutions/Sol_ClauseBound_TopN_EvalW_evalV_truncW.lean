-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.evalV_truncW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:16.801298+00:00
-- url     : https://prove2.me/submissions/6a7b2942-5a39-4dfb-b026-642473c4cd4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_ClauseBound_TopN_EvalW_evalV_weight
import Theorems.Thm_ClauseBound_TopN_EvalW_GW_congr
import Theorems.Thm_ClauseBound_TopN_EvalW_sum_vset_GW
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml)
    (ws : List ℤ) (lo hi : List ℕ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ p.2.1.length)
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → GW Ls.length ws lo hi (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => GW Ls.length ws lo hi (tl gu.length c.2.1 c.2.2) * val c) p Ls = truncW p.1.length ws lo hi Ls := by
  rw [evalV_weight hV hP k pad gu val p Ls (GW Ls.length ws lo hi) hg hb hb' hW hpad (GW_congr Ls.length ws lo hi) hval]
  unfold truncW
  exact sum_congr rfl fun σ _ => sum_vset_GW (Mark.ext σ) p.2.1.length ws lo hi Ls hw
end ClauseBound.TopN.EvalW
