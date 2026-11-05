-- Prove2me | solution 1 for ClauseBound.Alg.Descend.two_pow_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:43.763863+00:00
-- url     : https://prove2.me/submissions/39469b95-81fa-484d-a891-4866d9f120d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists
namespace ClauseBound.Alg.Descend
theorem _root_.solution {n : ℕ} (h : 1 ≤ n) : 2 ^ Nat.size n ≤ 2 * n := by
  have h0 : 0 < Nat.size n := Nat.size_pos.2 h
  have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1
end ClauseBound.Alg.Descend
