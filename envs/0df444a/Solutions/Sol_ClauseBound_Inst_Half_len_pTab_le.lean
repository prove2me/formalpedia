-- Prove2me | solution 1 for ClauseBound.Inst.Half.len_pTab_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:25:25.750293+00:00
-- url     : https://prove2.me/submissions/5929f8fc-a6d1-45d1-98d7-8a74832e8c58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_ClauseBound_Inst_Half_len_le_of_forall
import Theorems.Thm_ClauseBound_Inst_Half_length_pTab
import Theorems.Thm_ClauseBound_Inst_Half_pTab_eq
import Theorems.Thm_ClauseBound_Part_p_le_two_pow


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution (j : ℕ) : len (pTab j) ≤ (j + 1) * (3 * (j + 1) + 4) + 2 := by
  have h := len_le_of_forall (c := 3 * (j + 1) + 2) (pTab j) fun a ha => by
    rw [pTab_eq] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi' := List.mem_range.1 hi
    have : Nat.size (p i) ≤ j + 1 := Nat.size_le.2 ((p_le_two_pow i).trans_lt (Nat.pow_lt_pow_right (by norm_num) hi'))
    rw [len_nat]
    omega
  rw [length_pTab] at h
  exact h
end ClauseBound.Inst.Half
