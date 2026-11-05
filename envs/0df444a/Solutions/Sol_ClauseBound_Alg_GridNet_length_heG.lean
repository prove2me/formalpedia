-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.length_heG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:34:28.047385+00:00
-- url     : https://prove2.me/submissions/b87f3d96-0520-4b75-aa9b-d26e59193943

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution {p d ℓ : ℕ} {tr : Bool} {z : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ) {x u : ℕ}
    (hx : x < nMemb p d tr) (hu : u < p * d) : (heG p d ℓ z x u).length = ℓ := by
  have h1 : (block (p * d * ℓ) x z).length = p * d * ℓ := length_block (by
    rw [hz, Nat.mul_assoc (nMemb p d tr)]
    exact Nat.mul_le_mul_right _ hx)
  exact length_block (by rw [h1]; exact Nat.mul_le_mul_right _ hu)
end ClauseBound.Alg.GridNet
