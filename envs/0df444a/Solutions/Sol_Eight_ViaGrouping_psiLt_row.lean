-- Prove2me | solution 1 for Eight.ViaGrouping.psiLt_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:24.79303+00:00
-- url     : https://prove2.me/submissions/91e39f49-313f-4ecd-b53a-2af4a188d4e2

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
import Theorems.Thm_Eight_ViaGrouping_psiLt_eq
import Theorems.Thm_Eight_ViaGrouping_A_bitsOf
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
import Theorems.Thm_Eight_Level_digOf_le
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
import Theorems.Thm_P2M_Eight_rowNetwork___891e43b2654c
import Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    psiLt g false lam y a b z z' = (netOfι g false lam y Rm).Ψ a b z z' := by
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g false o i)).length = lam := fun w hw o x i =>
    length_heG (tr := false) hw x.2 (nodeG_lt (p := g) false o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g false lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g false w'.1 w'.2)) :=
    fun w x w' => stC_dec g g false lam w x w'
  rw [psiLt_eq, netOfι_row]
  refine Eq.trans ?_ (Network.Ψ_pull (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ a b z z').symm
  refine Eq.trans ?_ (rowNetwork_Ψ hlam (gridR0 g g lam Rm) (digOf_le g lam y) hab _ _).symm
  congr 1
  · refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [hd, hd]
    exact (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).symm
  · refine prod_congr rfl fun k _ => ?_
    rw [hd, hd, hd, hd, A_bitsOf _ (hl z hz b k.1 k.2) (hl z hz b k.2 k.1) (hl z' hz' a k.1 k.2) (hl z' hz' a k.2 k.1)]
    rfl
end Eight.ViaGrouping
