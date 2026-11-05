-- Prove2me | solution 1 for ClauseBound.ParityChecks.occOL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:40.376309+00:00
-- url     : https://prove2.me/submissions/9e448206-5a6a-41e5-b5ff-215e9be1ebe7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_colMax_le
import Theorems.Thm_ClauseBound_ParityChecks_rowMax_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : occOL n Δ + 4 ≤ 19 * Δ * (LD Δ + Nat.clog 2 n + 1) := by
  unfold occOL
  have hc := colMax_le hn hΔ
  have hr := rowMax_le hn hΔ
  generalize colMax n Δ = cm at hc ⊢
  generalize rowMax n Δ = rm at hr ⊢
  generalize LD Δ = L at hc hr ⊢
  generalize Nat.clog 2 n = c at hc hr ⊢
  have e : 19 * Δ * (L + c + 1) = 19 * (Δ * L) + 19 * (Δ * c) + 19 * Δ := by ring
  have h1 : Δ * (2 + cm) ≤ Δ * (19 * L + c + 8) := Nat.mul_le_mul_left _ (by omega)
  have e1 : Δ * (19 * L + c + 8) = 19 * (Δ * L) + Δ * c + 8 * Δ := by ring
  have e2 : 3 * Δ * L = 3 * (Δ * L) := by ring
  have h2 : c ≤ Δ * c := Nat.le_mul_of_pos_left _ (by omega)
  rw [e]
  rcases le_total (Δ * (2 + cm)) rm with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega
end ClauseBound.ParityChecks
