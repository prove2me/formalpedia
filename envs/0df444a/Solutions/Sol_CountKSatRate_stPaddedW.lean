-- Prove2me | solution 1 for CountKSatRate.stPaddedW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:09.415184+00:00
-- url     : https://prove2.me/submissions/014de25f-4ede-4ca6-9b02-3b7f6238e5fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_CountKSatRate_Pad_padMW_runs
import Theorems.Thm_CountKSatRate_Pad_len_padded
import Theorems.Thm_CountKSat_stHostW
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PB_pow
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
open CountKSatRate
open Groundwork PaddedDescent Turing Pad
namespace CountKSatRate
theorem _root_.solution : StPaddedW := by
  intro e B he hB
  have hI := padMW_isPolyT he hB
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.stHostW (padMW e B)
  obtain ⟨-, tB, pB, mB, -, lB⟩ := hB.elim
  have pW : PB fun m => 2 * tB (4 * m + 6) + 2 :=
    ((PB.const 2).mul (pB.comp (((PB.const 4).mul PB.id').add (PB.const 6)))).add (PB.const 2)
  have pQ : PB fun m => q₀ * (m + 2) * (m + (2 * m + 3 + (2 * tB (4 * m + 6) + 2)) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 2))).mul
      (((PB.id'.add ((((PB.const 2).mul PB.id').add (PB.const 3)).add pW)).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pQ
  refine ⟨N, q, hfin, fun x => ?_⟩
  obtain ⟨ev⟩ := hN x _ _ _ (padMW_runs e B x)
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, m = x.length + 2 ^ e x := ⟨_, rfl⟩
  have h0 : e x < 2 ^ e x := Nat.lt_two_pow_self
  have hw : (B (x, pad (e x))).length ≤ tB (4 * m + 6) := by
    have a1 := lB (x, pad (e x))
    rw [len_bools, len_padded] at a1
    have a2 : tB (3 * x.length + 4 * 2 ^ e x + 6) ≤ tB (4 * m + 6) := mB (by omega)
    omega
  have h1 : e x + 1 + 1 ≤ m + 2 := by omega
  have h2 : x.length + (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) + 1 ≤
      m + (2 * m + 3 + (2 * tB (4 * m + 6) + 2)) + 1 := by omega
  rw [← hm]
  exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 q₀)).trans (hq m)
end CountKSatRate
