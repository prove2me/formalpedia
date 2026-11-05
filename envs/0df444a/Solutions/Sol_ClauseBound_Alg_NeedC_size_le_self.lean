-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.size_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:07.243873+00:00
-- url     : https://prove2.me/submissions/24bf92fe-97b3-4b8e-8685-fba040295024

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (m : ℕ) : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self
end ClauseBound.Alg.NeedC
