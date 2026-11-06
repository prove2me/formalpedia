-- Prove2me | solution 1 for CircuitLowerBound.room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:11:01.838913+00:00
-- url     : https://prove2.me/submissions/316ef6f5-2260-456c-b51e-eeaff9f45098

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
import Theorems.Thm_CircuitLowerBound_lin_le_two_pow

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
theorem _root_.solution {e : MCode} {L P : ℕ} (hL : 4 * (kb e + lam e) + 64 ≤ L) (hP : P ≤ 3 * L) : Fits e L P ∧ P / 8 ≤ bt e L := by
  have hb : 3 * L / 8 ≤ bt e L := by unfold bt; omega
  refine ⟨⟨by omega, ?_⟩, by omega⟩
  have h1 := lin_le_two_pow (L / 8) (by omega)
  have h2 : 2 ^ (L / 8) ≤ 2 ^ bt e L := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
end CircuitLowerBound
