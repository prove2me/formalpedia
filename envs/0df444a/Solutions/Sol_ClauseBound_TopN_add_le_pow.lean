-- Prove2me | solution 1 for ClauseBound.TopN.add_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:35:30.800516+00:00
-- url     : https://prove2.me/submissions/2159d15c-490d-45dc-a1cb-1eb15792a0f3

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
theorem _root_.solution {x y p q r : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) (hp : p < r) (hq : q < r) : x + y ≤ 2 ^ r := by
  obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  have h1 : 2 ^ p ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ q ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega
end ClauseBound.TopN
