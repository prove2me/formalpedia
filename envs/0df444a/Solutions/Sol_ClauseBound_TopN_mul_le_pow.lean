-- Prove2me | solution 1 for ClauseBound.TopN.mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:11:47.818326+00:00
-- url     : https://prove2.me/submissions/04ed09a1-4659-444e-b531-e438a66eea93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)
namespace ClauseBound.TopN
theorem _root_.solution {x y p q : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) : x * y ≤ 2 ^ (p + q) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy
end ClauseBound.TopN
