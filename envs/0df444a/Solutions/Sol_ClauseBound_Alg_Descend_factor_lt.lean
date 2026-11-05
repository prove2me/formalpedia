-- Prove2me | solution 1 for ClauseBound.Alg.Descend.factor_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:49:40.679099+00:00
-- url     : https://prove2.me/submissions/c8e908b9-f45f-4be5-985e-f4e699ca8db7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists
namespace ClauseBound.Alg.Descend
theorem _root_.solution {f D z r x : ℕ} (hf : f < 2 ^ z) (hD : D ≤ 2 ^ r) : f * D < 2 ^ (z + r + x) := by
  calc f * D ≤ f * 2 ^ r := Nat.mul_le_mul_left _ hD
    _ < 2 ^ z * 2 ^ r := Nat.mul_lt_mul_of_pos_right hf (by positivity)
    _ = 2 ^ (z + r) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (z + r + x) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
end ClauseBound.Alg.Descend
