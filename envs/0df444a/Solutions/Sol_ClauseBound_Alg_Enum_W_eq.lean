-- Prove2me | solution 1 for ClauseBound.Alg.Enum.W_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:06.047145+00:00
-- url     : https://prove2.me/submissions/d2afee0c-c1ff-4e32-8fd6-29bfae44f6b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_Runs_unique
import Theorems.Thm_PaddedDescent_F_RebalF_freeM_runs
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (hN : F.toP.Presents c N 0 0) (a : Fin g) (z : List Bool) (hz : z.length = F.n c a) :
    F.W (c, (a.val, z)) = N.W a z :=
  (RebalF.freeM_runs F.W _).unique (hN.W_runs a z hz)
end ClauseBound.Alg.Enum
