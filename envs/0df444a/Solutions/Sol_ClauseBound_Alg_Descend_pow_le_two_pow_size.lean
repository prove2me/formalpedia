-- Prove2me | solution 1 for ClauseBound.Alg.Descend.pow_le_two_pow_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:42.617962+00:00
-- url     : https://prove2.me/submissions/f3313a09-653c-4d31-873d-fc82226df220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists
namespace ClauseBound.Alg.Descend
theorem _root_.solution (d R : ℕ) : d ^ R ≤ 2 ^ (R * Nat.size d) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self d).le R
end ClauseBound.Alg.Descend
