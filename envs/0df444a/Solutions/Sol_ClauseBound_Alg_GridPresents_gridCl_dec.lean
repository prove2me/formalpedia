-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.gridCl_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:12.650531+00:00
-- url     : https://prove2.me/submissions/b71deb3b-37f5-4f0c-b0d4-6e48b469c74d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (gridCl P pad p d tr h ℓ y R a b).dec = ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).dec := by
  unfold gridCl
  rw [dif_pos hab]
  rfl
end ClauseBound.Alg.GridPresents
