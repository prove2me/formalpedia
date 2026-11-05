-- Prove2me | solution 1 for ClauseBound.ParityChecks.colMax_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:07.775972+00:00
-- url     : https://prove2.me/submissions/9dfdd2ca-c5cc-405b-bc0e-9f3c1b7f2cdd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_Sizes_two_mul_le
import Theorems.Thm_ClauseBound_ParityChecks_Sizes_le_two_pow_clog

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : colMax n Δ ≤ 19 * LD Δ + Nat.clog 2 n + 6 := by
  have _ := hn
  have _ := hΔ
  unfold colMax
  have h1 : Nat.clog 2 (16 * Δ * n) ≤ 4 + LD Δ + Nat.clog 2 n := by
    refine Nat.clog_le_of_le_pow ?_
    have h2 : Δ ≤ 2 ^ LD Δ := by have := two_mul_le Δ; omega
    calc 16 * Δ * n ≤ 16 * 2 ^ LD Δ * 2 ^ Nat.clog 2 n := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (le_two_pow_clog n)
      _ = 2 ^ (4 + LD Δ + Nat.clog 2 n) := by ring
  omega
end ClauseBound.ParityChecks
