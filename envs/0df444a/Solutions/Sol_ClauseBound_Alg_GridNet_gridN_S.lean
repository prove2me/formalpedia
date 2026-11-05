-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.gridN_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:32.994364+00:00
-- url     : https://prove2.me/submissions/ff0508c9-772a-46c3-87ca-1453eff2916a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
variable (P pad p d tr h ℓ y)
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) :
    (gridN P pad p d tr h ℓ y Rm).S a = words (nMemb p d tr * (p * d) * ℓ) := rfl
end ClauseBound.Alg.GridNet
