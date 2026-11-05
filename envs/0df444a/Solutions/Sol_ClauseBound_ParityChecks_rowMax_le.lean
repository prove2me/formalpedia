-- Prove2me | solution 1 for ClauseBound.ParityChecks.rowMax_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:08.742295+00:00
-- url     : https://prove2.me/submissions/59199e82-a0d3-4a4f-a1b3-a64b11018987

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_Sizes_le_two_pow_clog

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : rowMax n Δ ≤ 3 * Δ * LD Δ + Nat.clog 2 n + 9 := by
  have _ := hn
  have _ := hΔ
  unfold rowMax
  have h1 : Nat.clog 2 (96 * n) ≤ 7 + Nat.clog 2 n := by
    refine Nat.clog_le_of_le_pow ?_
    calc 96 * n ≤ 128 * 2 ^ Nat.clog 2 n := Nat.mul_le_mul (by norm_num) (le_two_pow_clog n)
      _ = 2 ^ (7 + Nat.clog 2 n) := by ring
  omega
end ClauseBound.ParityChecks
