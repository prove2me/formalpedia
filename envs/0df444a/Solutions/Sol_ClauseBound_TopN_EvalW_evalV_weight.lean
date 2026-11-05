-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.evalV_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:19:57.586241+00:00
-- url     : https://prove2.me/submissions/6bdae9e3-21af-4b45-8de3-aecadef6daa1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_ClauseBound_TopN_EvalW_evalV_weight_aux
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
theorem _root_.solution (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) p Ls =
      ∑ σ : Fin p.1.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ p.2.1.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by
  obtain ⟨nu, wu, βu, bu⟩ := p
  exact evalV_weight_aux hV hP k pad gu val nu wu βu bu Ls G hg hb hb' hW hpad hG hval
end ClauseBound.TopN.EvalW
