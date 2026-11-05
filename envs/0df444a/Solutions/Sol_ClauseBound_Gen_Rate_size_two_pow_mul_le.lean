-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_two_pow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:56.886955+00:00
-- url     : https://prove2.me/submissions/0c8a30c0-16d9-4aa0-b6d2-cd11639cf3e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
import Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (k b : ℕ) : size (2 ^ k * b) ≤ k + 1 + size b := by
  have := size_mul_le (2 ^ k) b
  rwa [Nat.size_pow] at this
end ClauseBound.Gen.Rate
