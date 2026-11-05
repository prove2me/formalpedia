-- Prove2me | solution 1 for ClauseBound.Alg.Enum.pos_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:48:47.652128+00:00
-- url     : https://prove2.me/submissions/88c1091b-ec7b-4f7f-b2ea-e2bc878a2d2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {g : ℕ}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (p : Fin g × Fin g) : pos p % g = p.2.val := by
  rw [pos, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.2]
end ClauseBound.Alg.Enum
