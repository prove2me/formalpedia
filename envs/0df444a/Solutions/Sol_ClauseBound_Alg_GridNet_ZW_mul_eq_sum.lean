-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.ZW_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:14.859291+00:00
-- url     : https://prove2.me/submissions/1064d336-f413-40a5-b566-b9a4fd095630

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976
import Theorems.Thm_ClauseBound_Alg_GridNet_sum_patG
import Theorems.Thm_ClauseBound_Alg_GridNet_cross_eq
import Theorems.Thm_ClauseBound_Grid_Z_mul_eq_sum
import Theorems.Thm_Groundwork_Grid_ZW_eq_Z


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n : ℕ) (D : ℤ)
    (hA : ∀ x y u v, ∑ i ∈ range (n + 1), A i x y u v = D * Pieces.cross x y u v) :
    D ^ nRectG p d * Inst.ZW ℓ [] Rm = ∑ y ∈ range ((n + 1) ^ nRectG p d), termZ p d ℓ Rm A n y := by
  rw [ZW_eq_Z ℓ Rm (fun _ => false), ← card_Ω_eq,
    ClauseBound.Grid.Z_mul_eq_sum (instW ℓ Rm) (fun _ => false) (finProdFinEquiv (m := p) (n := d)).symm (range (n + 1)) 0 A D
      (fun x y u v => by rw [hA, cross_eq]), card_Ω_eq, ← sum_patG]
  rfl
end ClauseBound.Alg.GridNet
