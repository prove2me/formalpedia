-- Prove2me | solution 1 for ClauseBound.Both.End.steps_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:31.662142+00:00
-- url     : https://prove2.me/submissions/b56ef3a4-74c6-482a-9ad2-d00a6daa8637

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_Both_End

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Both ClauseBound.Both.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
namespace ClauseBound.Both.End
theorem _root_.solution (q : ℕ) {L L' E E' : ℕ} (hL : L ≤ L') (hE : E ≤ E') : q * (L + 2 ^ E + 1) ^ q ≤ q * (L' + 2 ^ E' + 1) ^ q :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hL (Nat.pow_le_pow_right (by norm_num) hE)) _) _)
end ClauseBound.Both.End
