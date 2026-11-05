-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.gridE_symm_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:48.777278+00:00
-- url     : https://prove2.me/submissions/262113e2-acae-4b46-b360-dbf29d706b19

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
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) (tr : Bool) (w : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    ((gridE p d tr).symm w : ℕ) = nodeG d tr w.1 w.2 := by
  cases tr <;> rfl
end ClauseBound.Alg.GridNet
