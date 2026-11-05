-- Prove2me | solution 1 for ClauseBound.ParityChecks.Ev.evalV_valS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:33.66549+00:00
-- url     : https://prove2.me/submissions/e2326ec2-9450-4d69-802d-46e9cf314bcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Theorems.Thm_ClauseBound_ParityChecks_Ev_sized_mono
import Theorems.Thm_ClauseBound_TopN_EvalW_evalV_truncW_ctx
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_sized_mono
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW
namespace ClauseBound.ParityChecks.Ev
theorem _root_.solution (hV : StMarkVal) (hP : StProfSum) (hPr : StMarkPresents) (hSz : StMarkSized) (hVal : StValS)
    {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (gu nu wu βu bu : U) (D U₀ P₀ : ℕ)
    (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hok : ok i) (hK : 2 ≤ S.K i) (hgu : gu.length = 3 * S.K i ^ 8) (hb : 0 < bu.length)
    (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls) (hocc : ∀ v, (occ Ls.flatten v).length ≤ D)
    (hfl : Ls.flatten.length ≤ bu.length * (nu.length + 1)) (hhi : ∀ l < Ls.length, hi.getD l 0 ≤ wu.length)
    (hprof : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hU : Ub k gu.length nu.length wu.length βu.length Ls.length ≤ U₀) (hP₀ : Pb gu.length nu.length βu.length D ≤ P₀)
    (hnet : 2 ^ needNet S i U₀ P₀ 0 ≤ pad.length) :
    evalV k pad gu (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * valS S pad i U₀ P₀ markF c) (nu, wu, βu, bu) Ls =
      truncW nu.length ws lo hi Ls := by
  have hg : 0 < gu.length := by
    rw [hgu]
    have : 0 < S.K i := by omega
    positivity
  have hVal' : ∀ g : ℕ, g = 3 * S.K i ^ 8 → ∀ (c : MCtx) (N : Network (Fin g) (List Bool) (List Bool)),
      markF.toP.Presents c N 0 0 → N.Sized P₀ 0 → N.U ≤ U₀ → valS S pad i U₀ P₀ markF c = N.value := by
    intro g hg'
    subst hg'
    intro c N h1 h2 h3
    exact hVal Idx S ok hC MCtx markF c pad i N U₀ P₀ 0 hok hK h1 h2 h3 hnet
  refine evalV_truncW_ctx hV hP k pad gu _ (nu, wu, βu, bu) Ls ws lo hi hg hb hb' hW hprof hhi fun y hy _ => ?_
  obtain ⟨h1, h2⟩ := hSz k gu nu βu bu wu.length D Ls y hg hb hb' hW hocc hfl hy
  exact hVal' gu.length hgu ((gu, nu, βu, bu), (Ls, y)) _ (hPr ((gu, nu, βu, bu), (Ls, y))) (sized_mono h1 hP₀) (h2.trans hU)
end ClauseBound.ParityChecks.Ev
