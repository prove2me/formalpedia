-- Prove2me | solution 1 for ClauseBound.ParityChecks.g_mul_PbOL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:00.074969+00:00
-- url     : https://prove2.me/submissions/27345626-9309-447c-a3f9-8ae0807737fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_Sizes_mul_qv_le
import Theorems.Thm_ClauseBound_ParityChecks_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_bitOL_le
import Theorems.Thm_ClauseBound_ParityChecks_occOL_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (K : ℕ) : 3 * K ^ 8 * PbOL K n Δ ≤ 1330 * (n + K ^ 8) * Δ * LD Δ * (LD Δ + Nat.clog 2 n + 1) := by
  unfold PbOL Pb
  have hb := bitOL_le hΔ
  have hL := two_le_LD hΔ
  have ho := occOL_le hn hΔ
  have hq := mul_qv_le (3 * K ^ 8) (7 * n)
  have h1 : 2 * (2 + bitOL Δ) ≤ 10 * LD Δ := by omega
  have h2 : 3 * K ^ 8 * qv (3 * K ^ 8) (7 * n) ≤ 7 * (n + K ^ 8) := by omega
  calc 3 * K ^ 8 * (2 * (2 + bitOL Δ) * qv (3 * K ^ 8) (7 * n) * (occOL n Δ + 4))
      = 2 * (2 + bitOL Δ) * (3 * K ^ 8 * qv (3 * K ^ 8) (7 * n)) * (occOL n Δ + 4) := by ring
    _ ≤ 10 * LD Δ * (7 * (n + K ^ 8)) * (19 * Δ * (LD Δ + Nat.clog 2 n + 1)) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) ho
    _ = 1330 * (n + K ^ 8) * Δ * LD Δ * (LD Δ + Nat.clog 2 n + 1) := by ring
end ClauseBound.ParityChecks
