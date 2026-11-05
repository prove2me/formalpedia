-- Prove2me | solution 1 for ClauseBound.Alg.Enum.enumLen_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:51:34.322254+00:00
-- url     : https://prove2.me/submissions/ddf6a70b-b3db-4743-8dcb-e8cb36d0b1e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_pos_div
import Theorems.Thm_ClauseBound_Alg_Enum_pos_mod

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (p : Fin g × Fin g) : enumLen g F c (pos p) = if p.1 < p.2 then F.cap c p.1 p.2 else 0 := by
  rw [enumLen, pos_div, pos_mod]
  rfl
end ClauseBound.Alg.Enum
