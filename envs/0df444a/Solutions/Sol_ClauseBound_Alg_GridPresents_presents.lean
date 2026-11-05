-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.presents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:07.029469+00:00
-- url     : https://prove2.me/submissions/4a282330-1557-4692-a003-21f8ee96c821

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridFf_eq
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridW_eq_W
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_f
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_lab
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_presents
import Theorems.Thm_PaddedDescent_F_RebalF_presents
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (P : PiecesF) (pad pu du hu ℓu : U) (tr : Bool) (y : ℕ) (T : Tab) :
    (gridF P).toP.Presents ((pad, (pu, du), tr, hu), (ℓu, y, T))
      (gridN P pad pu.length du.length tr hu.length ℓu.length y (instOf (K := pu.length * du.length) T)) 0 0 := by
  refine RebalF.presents (gridF P) _ _ (fun a => rfl) (fun a b hab => gridN_c _ _ _ _ _ _ _ _ _ hab)
    (fun a b hab => gridN_lab _ _ _ _ _ _ _ _ _ hab) (fun a z hz => ?_) (fun a b z θ hab hz hθ => ?_)
  · exact gridW_eq_W P pad pu.length du.length tr hu.length ℓu.length y T a hz
  · change gridFf P pad pu.length du.length tr hu.length ℓu.length y ((a.val, b.val), (z, θ)) = _
    rw [gridFf_eq, gridN_f P pad pu.length du.length tr hu.length ℓu.length y _ hab hz hθ]
end ClauseBound.Alg.GridPresents
