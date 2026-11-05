-- Prove2me | solution 1 for ClauseBound.Alg.Need.pow_le_two_pow_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:55.435776+00:00
-- url     : https://prove2.me/submissions/7b92b934-56d4-48ef-8f61-9dcd585b2cb2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F
namespace ClauseBound.Alg.Need
theorem _root_.solution (K p : ℕ) : K ^ p ≤ 2 ^ (p * Nat.size K) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self K).le p
end ClauseBound.Alg.Need
