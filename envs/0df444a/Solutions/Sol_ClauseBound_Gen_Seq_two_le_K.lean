-- Prove2me | solution 1 for ClauseBound.Gen.Seq.two_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:17:09.688326+00:00
-- url     : https://prove2.me/submissions/64560ed7-5267-49f7-9527-51416d52df06

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Seq
import Theorems.Thm_ClauseBound_Gen_K_eq
import Theorems.Thm_ClauseBound_Gen_x_ge


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.Seq
namespace ClauseBound.Gen.Seq
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ≤ K x₀ l := by
  rw [K_eq]
  have := x_ge x₀ l hx
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ x x₀ l := Nat.pow_le_pow_right (by norm_num) (by omega)
end ClauseBound.Gen.Seq
