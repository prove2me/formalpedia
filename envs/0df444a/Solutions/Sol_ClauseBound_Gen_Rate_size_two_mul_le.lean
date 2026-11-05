-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:52.429064+00:00
-- url     : https://prove2.me/submissions/642a6e4a-e943-4118-8b58-46d59a3bb5da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (a : ℕ) : size (2 * a) ≤ size a + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self a
  omega
end ClauseBound.Gen.Rate
