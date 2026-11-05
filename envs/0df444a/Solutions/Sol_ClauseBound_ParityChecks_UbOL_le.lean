-- Prove2me | solution 1 for ClauseBound.ParityChecks.UbOL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:52.815781+00:00
-- url     : https://prove2.me/submissions/44b563e7-878d-4eea-bfd5-f3cd0e2769fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_bitOL_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (k K : ℕ) : UbOL k K n Δ ≤ 354 * k * n * LD Δ + 6 * (3 * K ^ 8) ^ 2 := by
  unfold UbOL Ub
  have hb := bitOL_le hΔ
  have hL := two_le_LD hΔ
  generalize bitOL Δ = b at hb ⊢
  generalize LD Δ = L at hb hL ⊢
  generalize 3 * K ^ 8 = g
  rw [Nat.add_sub_cancel]
  have h1 : 11 * n * (1 + b) ≤ 11 * n * (2 * L + 5) := Nat.mul_le_mul_left _ (by omega)
  have h2 : n * 2 ≤ n * L := Nat.mul_le_mul_left _ hL
  have h3 : 11 * n * (1 + b) + (7 * n + 1) ≤ 59 * (n * L) := by
    have e : 11 * n * (2 * L + 5) = 22 * (n * L) + 55 * n := by ring
    omega
  calc 2 * 3 * (k * (11 * n) * (1 + b) + k * (7 * n + 1) + g ^ 2) = 6 * (k * (11 * n * (1 + b) + (7 * n + 1))) + 6 * g ^ 2 := by ring
    _ ≤ 6 * (k * (59 * (n * L))) + 6 * g ^ 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)) _
    _ = 354 * k * n * L + 6 * g ^ 2 := by ring
end ClauseBound.ParityChecks
