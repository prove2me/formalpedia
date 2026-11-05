-- Prove2me | solution 1 for ClauseBound.Alg.Enum.f_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:07.147147+00:00
-- url     : https://prove2.me/submissions/00c9e473-5c3c-4e24-bb5d-92eed091b1a8

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
theorem _root_.solution (hN : F.toP.Presents c N 0 0) (a b : Fin g) (z θ : List Bool) (hab : a ≠ b) (hz : z.length = F.n c a)
    (hθ : θ.length = F.cap c a b) : F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ :=
  (RebalF.freeM_runs F.f _).unique (hN.f_runs a b z θ hab hz hθ)
end ClauseBound.Alg.Enum
