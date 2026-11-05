-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_eight_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:53.555995+00:00
-- url     : https://prove2.me/submissions/c7979b29-e192-4174-a6e9-e3d38f955c2d

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
theorem _root_.solution (a : ℕ) : size (8 * a) ≤ size a + 3 := by
  rw [Nat.size_le, pow_add]
  have := Nat.lt_size_self a
  omega
end ClauseBound.Gen.Rate
