-- Prove2me | solution 1 for Eight.eqExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:34.32219+00:00
-- url     : https://prove2.me/submissions/d0d8cd8e-ecac-4e6c-8d22-67d175588a0f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_ClauseBound_Alg_GridNet_cross_eq
import Theorems.Thm_ClauseBound_Grid_Z_mul_eq_sum
import Theorems.Thm_Eight_a_sum
import Theorems.Thm_Eight_lemPieces
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}
namespace Eight
theorem _root_.solution {J : Type} [Fintype J] [LinearOrder J] (hlam : 1 ≤ lam) (W : Inst J (Bits lam)) (d : Bits lam) (e : J ≃ Fin g × Fin g) :
    2 ^ (tOf lam * #(rectangles g)) * W.Z d = ∑ ι ∈ patterns g lam, Zι (Grid.onGrid W d e) ι := by
  rw [pow_mul]
  exact ClauseBound.Grid.Z_mul_eq_sum W d e (range (tOf lam + 1)) 0 (fun i => Eight.A lam i) (2 ^ tOf lam) fun x y u v => by
    rw [lemPieces.a_sum lam hlam, ClauseBound.Alg.GridNet.cross_eq]
end Eight
