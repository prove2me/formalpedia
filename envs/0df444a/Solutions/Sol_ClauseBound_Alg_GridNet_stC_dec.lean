-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.stC_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:50:12.389199+00:00
-- url     : https://prove2.me/submissions/0bff5824-d34c-4a48-a37f-a78ccb472113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_gridE_symm_val
import Theorems.Thm_Groundwork_Grid_gridE_symm_val


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin (nMemb p d tr)) (w' : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    (stC p d tr n).dec z x w' = Grid.bitsOf n (heG p d n z x (nodeG d tr w'.1 w'.2)) := by
  rw [← gridE_symm_val]
  rfl
end ClauseBound.Alg.GridNet
