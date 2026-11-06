-- Prove2me | solution 1 for Eight.ViaGrouping.gridPsi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:00.935195+00:00
-- url     : https://prove2.me/submissions/1f9bfc6d-8a56-49a1-ab86-15832ae2b665

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
import Theorems.Thm_P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    gridPsi g tr lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z' := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact (if_pos (Fin.lt_def.1 h)).trans (psiLt_eq_Ψ hlam tr y Rm h hz hz')
  · rw [Network.Ψ_comm]
    exact (if_neg (not_lt.2 (Fin.lt_def.1 h).le)).trans (psiLt_eq_Ψ hlam tr y Rm h hz' hz)
end Eight.ViaGrouping
