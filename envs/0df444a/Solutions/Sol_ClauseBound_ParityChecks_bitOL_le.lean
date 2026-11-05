-- Prove2me | solution 1 for ClauseBound.ParityChecks.bitOL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:48:56.297134+00:00
-- url     : https://prove2.me/submissions/7507a979-d326-4827-9024-d9535a4a9892

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_Sizes_two_mul_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hΔ : 2 ≤ Δ) : bitOL Δ ≤ 2 * LD Δ + 4 := by
  have _ := hΔ
  unfold bitOL blkOL
  refine Nat.clog_le_of_le_pow ?_
  have h1 := two_mul_le Δ
  generalize LD Δ = L at h1 ⊢
  have h2 : L < 2 ^ L := Nat.lt_two_pow_self
  have h3 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  calc 2 * Δ + 16 * Δ * L + 1 = 2 * Δ * (1 + 8 * L) + 1 := by ring
    _ ≤ 2 ^ L * (1 + 8 * L) + 2 ^ L * 1 := Nat.add_le_add (Nat.mul_le_mul_right _ h1) (by omega)
    _ = 2 ^ L * (8 * L + 2) := by ring
    _ ≤ 2 ^ L * (8 * 2 ^ L) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (2 * L + 3) := by ring
    _ ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
end ClauseBound.ParityChecks
