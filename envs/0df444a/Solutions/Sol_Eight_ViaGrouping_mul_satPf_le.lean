-- Prove2me | solution 1 for Eight.ViaGrouping.mul_satPf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:23.576214+00:00
-- url     : https://prove2.me/submissions/a3d4a04d-42db-4467-bf9b-8273de5efef7

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_SatNet_mul_size_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper
namespace Eight.ViaGrouping
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (g : ℕ) (Φ : Fml) : g * satPf g k Φ ≤ 2 * k * (Φ.length + g) := by
  unfold satPf
  rcases le_total 1 (2 * k * mu g Φ) with h | h
  · rw [max_eq_right h]; exact SatNet.mul_size_le Φ.length g k
  · rw [max_eq_left h, Nat.mul_one]
    calc g ≤ Φ.length + g := Nat.le_add_left _ _
      _ = 1 * (Φ.length + g) := (Nat.one_mul _).symm
      _ ≤ 2 * k * (Φ.length + g) := Nat.mul_le_mul_right _ (by omega)
end Eight.ViaGrouping
