-- Prove2me | solution 1 for ClauseBound.ParityChecks.size_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:59:36.9136+00:00
-- url     : https://prove2.me/submissions/e658602e-386d-4d91-8c29-767a964d2b36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks
theorem _root_.solution (β n : ℕ) : Nat.size (2 ^ β * n) ≤ β + Nat.size n := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self n) (by positivity)
end ClauseBound.ParityChecks
