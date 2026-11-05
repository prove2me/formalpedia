-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.gridN_c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:09:19.562198+00:00
-- url     : https://prove2.me/submissions/8b672bbd-fcae-44bc-94ac-0419a77a0542

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_ClauseBound_Grid_rowNet_c_le_pd


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool))
    (a b : Fin (nParts p d tr)) : (gridN P pad p d tr h ℓ y Rm).c a b ≤ nMemb p d tr ^ 2 * (P.m * ℓ) :=
  ClauseBound.Grid.rowNet_c_le_pd hP.m_pos (Fintype.card_fin _) (gridR p d tr ℓ Rm) (cutsG P pad p d tr h ℓ y) []
    (fun _ => hP.cap_le tr _ (digG_lt hP.cnt_pos d tr y _ _)) a b
end ClauseBound.Alg.GridNet
