-- Prove2me | solution 1 for CircuitLowerBound.TabF.two_pow_nb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:14.077453+00:00
-- url     : https://prove2.me/submissions/10655fe3-c404-4bd9-b88b-7684803fcc10

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_two_pow_size_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution {e : MCode} {L P : ℕ} (hF : Fits e L P) : 2 ^ nb e L ≤ (2 * (tab e).length + 1) * 2 ^ L := by
  obtain ⟨h1, -⟩ := hF
  have h2 : bt e L + bq e L ≤ L := by
    unfold bq bt
    omega
  calc 2 ^ nb e L = 2 ^ rb e * 2 ^ (bt e L + bq e L) := by rw [nb, add_assoc, pow_add]
    _ ≤ (2 * (tab e).length + 1) * 2 ^ L := Nat.mul_le_mul (two_pow_size_le _) (Nat.pow_le_pow_right (by norm_num) h2)
end CircuitLowerBound.TabF
