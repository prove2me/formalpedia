-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.grid_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:19:59.691064+00:00
-- url     : https://prove2.me/submissions/b36aed63-4a6e-48d4-8374-e08da81e6be5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_bitsOf_bitsOf
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridCl_dec
import Theorems.Thm_ClauseBound_Alg_GridPresents_mem_gridCl_D
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_block_take
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (top : Bool) (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    (o : Fin (nParts p d tr)) {z θ : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ)
    (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    (if θ ∈ (gridCl P pad p d tr h ℓ y R a b).D then
      (∏ i : Fin (nMemb p d tr), if (stC p d tr ℓ).dec z i (o, i) = ((gridCl P pad p d tr h ℓ y R a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        if top = true then
          (cutsG P pad p d tr h ℓ y ((a, b), k)).top ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
        else
          (cutsG P pad p d tr h ℓ y ((a, b), k)).bot ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr o i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        (if top = true then P.top else P.bot) ((pad, tr), (h, digG P d tr h ℓ y (tri a b) (tri k.1 k.2)),
          (heG p d ℓ z k.1 (nodeG d tr o k.2), heG p d ℓ z k.2 (nodeG d tr o k.1),
            chunkAt (lenG P d tr h ℓ y (tri a b)) (tri k.1 k.2) (θ.drop (nMemb p d tr * ℓ)))) := by
  have hhe : ∀ x i : Fin (nMemb p d tr), (heG p d ℓ z x (nodeG d tr o i)).length = ℓ := fun x i =>
    length_heG hz x.2 (nodeG_lt tr o.2 i.2)
  rw [if_pos (mem_gridCl_D R hab hθ)]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [gridCl_dec R hab, GridNet.stC_dec]
    change (if Grid.bitsOf ℓ (heG p d ℓ z i (nodeG d tr o i)) = Grid.bitsOf ℓ (block ℓ i (θ.take (nMemb p d tr * ℓ))) then (1 : ℤ) else 0) = _
    rw [block_take _ i.2]
    exact if_congr (bitsOf_inj (hhe i i)
      (length_block (by rw [hθ]; exact (Nat.mul_le_mul_right _ i.2).trans (Nat.le_add_right _ _)))) rfl rfl
  · refine prod_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    have hd : ((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k =
        chunkAt (lenG P d tr h ℓ y (tri a b)) (tri k.1 k.2) (θ.drop (nMemb p d tr * ℓ)) := by
      rw [gridCl_dec R hab]
      change (if k.1 < k.2 then _ else _) = _
      rw [if_pos hk']
      rfl
    rw [hd, GridNet.stC_dec, GridNet.stC_dec]
    cases top
    · change P.bot ((pad, tr), (h, _), (ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), _)) = _
      rw [bitsOf_bitsOf (hhe k.1 k.2), bitsOf_bitsOf (hhe k.2 k.1)]
      rfl
    · change P.top ((pad, tr), (h, _), (ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), _)) = _
      rw [bitsOf_bitsOf (hhe k.1 k.2), bitsOf_bitsOf (hhe k.2 k.1)]
      rfl
end ClauseBound.Alg.GridPresents
