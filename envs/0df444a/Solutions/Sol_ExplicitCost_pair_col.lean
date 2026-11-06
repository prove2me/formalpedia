-- Prove2me | solution 1 for ExplicitCost.pair_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:39.590267+00:00
-- url     : https://prove2.me/submissions/8e91c68b-d91f-4cdb-bb30-fb79ad0ad8bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
import Theorems.Thm_ExplicitCost_cutsOK_piecesOf
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e
import Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    (gridN (piecesOf D c) [()] g g true 0 lam y Rm).Ψ a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g true b i) = heG g g lam z' i (nodeG g true a i) then 1 else 0) *
        ∏ k : Fin g × Fin g with k.1 < k.2, pieceValue D lam (indexAt D lam (digG (piecesOf D c) g true 0 lam y (tri a.val b.val) (tri k.1 k.2))) (rectStrings g true lam ((a.val, b.val), (z, z')) k.1 k.2) := by
  have hC := cutsOK_piecesOf hS hlam [()]
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g true o i)).length = lam := fun w hw o x i =>
    length_heG (tr := true) hw x.2 (nodeG_lt (p := g) true o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g true lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g true w'.1 w'.2)) :=
    fun w x w' => stC_dec g g true lam w x w'
  refine (Network.Ψ_pull (gridNet (piecesOf D c) [()] g g true 0 lam y (gridR g g true lam Rm)) _ _ _ a b z z').trans ?_
  refine (rowNet_Ψ (fun ω => hC.factors true _ (digG_lt hC.cnt_pos g true y _ _)) _ _ _ hab _ _).trans ?_
  unfold rowΨ
  congr 1
  refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun e => (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).1 ((hd z i (b, i)).symm.trans (e.trans (hd z' i (a, i)))),
    fun e => (hd z i (b, i)).trans (((bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).2 e).trans (hd z' i (a, i)).symm)⟩
end ExplicitCost
