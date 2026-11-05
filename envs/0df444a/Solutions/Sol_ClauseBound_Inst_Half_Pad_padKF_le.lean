-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.padKF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:17.503602+00:00
-- url     : https://prove2.me/submissions/af3c1965-4142-4ebe-ba91-df74eb76b3c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution (h Δ L : ℕ) (hL : L ≤ h) : padKF (4 * h) Δ h h L ≤ 2 ^ 10 * (h + 2) ^ 4 * (Δ + 1) ^ 2 := by
  unfold padKF
  have h1 : 3 * (h + (4 * (4 * h) + 1) * L) + 10 ≤ 48 * (h + 2) ^ 2 := by
    have : (4 * (4 * h) + 1) * L ≤ (4 * (4 * h) + 1) * h := Nat.mul_le_mul_left _ hL
    nlinarith
  have h2 : Δ ^ 2 ≤ (Δ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : 1 ≤ (Δ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨A, hA⟩ : ∃ A, A = h + 2 := ⟨_, rfl⟩
  have hA2 : 2 ≤ A := by omega
  have hh : h + 1 ≤ A := by omega
  rw [← hA] at h1 ⊢
  generalize (Δ + 1) ^ 2 = D at *
  generalize Δ ^ 2 = X at *
  generalize 3 * (h + (4 * (4 * h) + 1) * L) + 10 = Y at *
  have hAA : A ≤ A ^ 3 := Nat.le_self_pow (by norm_num) A
  have hZ : A ≤ A ^ 3 * D := le_trans hAA (Nat.le_mul_of_pos_right _ h3)
  calc (h + 1) * (X * Y + 4) + 2 ≤ A * (D * (48 * A ^ 2) + 4) + 2 := by gcongr
    _ = 48 * (A ^ 3 * D) + 4 * A + 2 := by ring
    _ ≤ 48 * (A ^ 3 * D) + 4 * (A ^ 3 * D) + A ^ 3 * D := by omega
    _ = 53 * (1 * (A ^ 3 * D)) := by ring
    _ ≤ 2 ^ 10 * (A * (A ^ 3 * D)) := by gcongr <;> omega
    _ = 2 ^ 10 * A ^ 4 * D := by ring
end ClauseBound.Inst.Half.Pad
