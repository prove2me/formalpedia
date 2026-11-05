-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.value_gridN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:38.19461+00:00
-- url     : https://prove2.me/submissions/18c6c8d0-3f91-4877-b763-2a603fb62927

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_full
import Theorems.Thm_ClauseBound_Alg_GridNet_ZG_gridR
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_Groundwork_Grid_stC_full
import Theorems.Thm_Groundwork_Grid_value_rowNet
import Theorems.Thm_Groundwork_Network_value_pull
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).value = termZ p d ℓ Rm A (P.cnt h ℓ - 1) y := by
  refine (Network.value_pull _ _ _ _ (fun _ => stC_full p d tr ℓ)).trans ?_
  rw [← ZG_gridR p d tr]
  exact value_rowNet (fun ω => hP.factors tr _ (digG_lt hP.cnt_pos d tr y _ _)) _ _ _
end ClauseBound.Alg.GridNet
