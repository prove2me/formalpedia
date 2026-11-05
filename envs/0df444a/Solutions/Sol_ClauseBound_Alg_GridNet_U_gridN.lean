-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.U_gridN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:19:52.880517+00:00
-- url     : https://prove2.me/submissions/9bf564f7-86e6-4407-9915-e59d8639ded0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533
import Theorems.Thm_ClauseBound_Grid_U_rowNet_pd


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).U = totalG P p d tr h ℓ y := by
  change (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).U = _
  unfold gridNet totalG priceG
  rw [ClauseBound.Grid.U_rowNet_pd (Fintype.card_fin _) (Fintype.card_fin _), ← sum_Ω_rectIxG p d tr]
  rfl
end ClauseBound.Alg.GridNet
