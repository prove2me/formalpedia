-- Prove2me | solution 1 for ClauseBound.Alg.Enum.pos_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:47:40.527217+00:00
-- url     : https://prove2.me/submissions/89482ad4-b010-4b70-93ee-4f0b8757d12f

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
theorem _root_.solution (p : Fin g × Fin g) : pos p / g = p.1.val := by
  have hg : 0 < g := p.1.pos
  rw [pos, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt p.2.2, Nat.zero_add]
end ClauseBound.Alg.Enum
