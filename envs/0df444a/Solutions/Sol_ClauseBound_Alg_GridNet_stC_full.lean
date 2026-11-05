-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.stC_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:11:08.179263+00:00
-- url     : https://prove2.me/submissions/a117660d-09df-4fc1-a8aa-813d85117faf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeC_full
import Theorems.Thm_Groundwork_Code_full_blocks
import Theorems.Thm_Groundwork_Code_full_cast
import Theorems.Thm_Groundwork_Grid_nodeC_full


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) (tr : Bool) (n : ℕ) : (stC p d tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (nodeC_full p d tr n))
end ClauseBound.Alg.GridNet
