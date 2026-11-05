-- Prove2me | solution 1 for Eight.ViaGrouping.size_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:47.624641+00:00
-- url     : https://prove2.me/submissions/fe24e6d0-4727-4cae-b2f2-6c550f940208

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper
namespace Eight.ViaGrouping
theorem _root_.solution {g k C₁ A s μ P : ℕ} (hμ : μ + 1 ≤ s) (hP : P ≤ 2 * (μ * k) + 1) (hA : (6 * k + 2 * g + 11) + C₁ * (2 * k + 3) ^ C₁ + C₁ + 1 ≤ A) :
    s + 2 * g + 6 * (μ * k) + 10 + C₁ * (s + P + 1) ^ C₁ ≤ A * s ^ A := by
  have hsk : μ * k + k ≤ s * k := by
    calc μ * k + k = (μ + 1) * k := by ring
      _ ≤ s * k := Nat.mul_le_mul_right k hμ
  have hgs : g ≤ g * s := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : s + 2 * g + 6 * (μ * k) + 10 ≤ (6 * k + 2 * g + 11) * s := by
    have : (6 * k + 2 * g + 11) * s = 6 * (s * k) + 2 * (g * s) + 11 * s := by ring
    omega
  have e2 : s + P + 1 ≤ (2 * k + 3) * s := by
    have : (2 * k + 3) * s = 2 * (s * k) + 3 * s := by ring
    omega
  have hs1 : 1 ≤ s := by omega
  have p1 : s ≤ s ^ A := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ A := Nat.pow_le_pow_right hs1 (by omega)
  have p2 : s ^ C₁ ≤ s ^ A := Nat.pow_le_pow_right hs1 (by omega)
  calc s + 2 * g + 6 * (μ * k) + 10 + C₁ * (s + P + 1) ^ C₁
      ≤ (6 * k + 2 * g + 11) * s + C₁ * ((2 * k + 3) * s) ^ C₁ := Nat.add_le_add e1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 _))
    _ = (6 * k + 2 * g + 11) * s + C₁ * (2 * k + 3) ^ C₁ * s ^ C₁ := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ (6 * k + 2 * g + 11) * s ^ A + C₁ * (2 * k + 3) ^ C₁ * s ^ A := Nat.add_le_add (Nat.mul_le_mul_left _ p1) (Nat.mul_le_mul_left _ p2)
    _ = ((6 * k + 2 * g + 11) + C₁ * (2 * k + 3) ^ C₁) * s ^ A := by ring
    _ ≤ A * s ^ A := Nat.mul_le_mul_right _ (by omega)
end Eight.ViaGrouping
