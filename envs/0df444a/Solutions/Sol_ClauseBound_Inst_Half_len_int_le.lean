-- Prove2me | solution 1 for ClauseBound.Inst.Half.len_int_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:22:55.688027+00:00
-- url     : https://prove2.me/submissions/b80d0d0f-c0be-4305-8535-dfcd7e2445c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {z : ℤ} {B : ℕ} (h : |z| ≤ 2 ^ B) : len z ≤ 3 * B + 8 := by
  have h1 : z.natAbs < 2 ^ (B + 1) := by
    have : (z.natAbs : ℤ) ≤ 2 ^ B := by rwa [Int.natCast_natAbs]
    have h2 : z.natAbs ≤ 2 ^ B := by exact_mod_cast this
    have h3 : 2 ^ B < 2 ^ (B + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h2 : Nat.size z.natAbs ≤ B + 1 := Nat.size_le.2 h1
  rw [len_int]
  omega
end ClauseBound.Inst.Half
