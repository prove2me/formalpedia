-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:00:22.77545+00:00
-- url     : https://prove2.me/submissions/5e49e64d-85fe-4f71-9a98-e9fcbc900ed0

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
theorem _root_.solution (n : ℕ) : size n ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self
end ClauseBound.Gen.Rate
