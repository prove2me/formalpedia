-- Prove2me | solution 1 for Eight.ViaGrouping.psiLt_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:59.934995+00:00
-- url     : https://prove2.me/submissions/9e56efcf-fc4b-4c33-a5ca-36aceb70dfcf

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
import Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
import Theorems.Thm_P2M_Eight_colNetwork___9ff9d9772d4b
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
    psiLt g true lam y a b z z' = (netOfι g true lam y Rm).Ψ a b z z' := by
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g true o i)).length = lam := fun w hw o x i =>
    length_heG (tr := true) hw x.2 (nodeG_lt (p := g) true o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g true lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g true w'.1 w'.2)) :=
    fun w x w' => stC_dec g g true lam w x w'
  rw [psiLt_eq, netOfι_col]
  refine Eq.trans ?_ (Network.Ψ_pull (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ a b z z').symm
  refine Eq.trans ?_ (colNetwork_Ψ hlam (gridR0 g g lam Rm) (digOf_le g lam y) hab _ _).symm
  congr 1
  · refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [hd, hd]
    exact (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).symm
  · refine prod_congr rfl fun k _ => ?_
    rw [hd, hd, hd, hd, A_bitsOf _ (hl z hz b k.1 k.2) (hl z' hz' a k.1 k.2) (hl z hz b k.2 k.1) (hl z' hz' a k.2 k.1)]
    rfl
end Eight.ViaGrouping
