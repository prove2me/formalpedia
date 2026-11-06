-- Prove2me | solution 1 for Eight.ViaGrouping.gridPsi_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:29.411579+00:00
-- url     : https://prove2.me/submissions/4ffaa391-3315-4f7e-bcf4-3e778f013e08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Eight_ViaGrouping_psiLt_polyT
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
variable {α : Type} [Enc α]
namespace Eight.ViaGrouping
theorem _root_.solution (g : ℕ) (tr : Bool) {lam y : α → ℕ} {q : α → PsiQ} (hl : PolyT lam) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => gridPsi g tr (lam x) (y x) (q x) :=
  PolyT.ite' (c := fun x => (q x).1.1 < (q x).1.2) (PolyT.decide_lt hq.fst.fst hq.fst.snd) (psiLt_polyT g tr hl hy hq.fst.fst hq.fst.snd hq.snd.fst hq.snd.snd)
    (psiLt_polyT g tr hl hy hq.fst.snd hq.fst.fst hq.snd.snd hq.snd.fst)
end Eight.ViaGrouping
