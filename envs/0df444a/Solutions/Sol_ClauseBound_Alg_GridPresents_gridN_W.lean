-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.gridN_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:15.887577+00:00
-- url     : https://prove2.me/submissions/4f45b6bd-12bc-4b97-84c5-ba186577fe9c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridR_nodeC
import Theorems.Thm_ClauseBound_Alg_GridNet_gridE_symm_val
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_gridE_symm_val
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) {z : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) :
    (gridN P pad p d tr h ℓ y Rm).W a z =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          Rm ((gridE p d tr).symm (a, i)) (fun u => if u = (gridE p d tr).symm (a, i) then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by
  have hn : ∀ i : Fin (nMemb p d tr), nodeG d tr a i < p * d := fun i => nodeG_lt tr a.2 i.2
  change rowW (gridR p d tr ℓ Rm) a ((stC p d tr ℓ).dec z) = _
  unfold rowW
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    have h1 := gridR_nodeC p d tr ℓ Rm (a, i) (wn := block (p * d * ℓ) i z) (length_block (by
      rw [hz, Nat.mul_assoc (nMemb p d tr)]
      exact Nat.mul_le_mul_right _ i.2))
    rw [GridNet.gridE_symm_val] at h1
    exact h1
  · refine prod_congr rfl fun q _ => if_congr ?_ rfl rfl
    rw [GridNet.stC_dec, GridNet.stC_dec]
    exact bitsOf_inj (length_heG hz q.1.2 (hn q.2)) (length_heG hz q.2.2 (hn q.1))
end ClauseBound.Alg.GridPresents
