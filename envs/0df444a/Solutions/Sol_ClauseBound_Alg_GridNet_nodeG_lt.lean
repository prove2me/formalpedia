-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.nodeG_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:49.618544+00:00
-- url     : https://prove2.me/submissions/98719675-c843-47bf-8c4b-8790a008229b

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
theorem _root_.solution {p d : ℕ} (tr : Bool) {a i : ℕ} (ha : a < nParts p d tr) (hi : i < nMemb p d tr) : nodeG d tr a i < p * d := by
  have h := ((gridE p d tr).symm (⟨a, ha⟩, ⟨i, hi⟩)).2
  rwa [gridE_symm_val] at h
end ClauseBound.Alg.GridNet
