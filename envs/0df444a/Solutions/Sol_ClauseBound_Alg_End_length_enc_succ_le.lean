-- Prove2me | solution 1 for ClauseBound.Alg.End.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:39:00.085217+00:00
-- url     : https://prove2.me/submissions/c3a28a8e-94bb-404c-ba6f-36c3dc4f555f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hn : n ≤ k * φ.length) :
    (SatM.enc k φ).length + 1 ≤ 8 * (k * φ.length) ^ 2 := by
  rw [length_enc]
  set m := φ.length
  have h1 : Nat.log2 (2 * n) ≤ 2 * n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self _ _
  have h2 : k ≤ k * m := Nat.le_mul_of_pos_right _ hm
  have h3 : 1 ≤ k * m := Nat.mul_pos hk hm
  have h4 : m * (k * (Nat.log2 (2 * n) + 1)) ≤ k * m * (2 * (k * m) + 1) := by
    calc m * (k * (Nat.log2 (2 * n) + 1)) = k * m * (Nat.log2 (2 * n) + 1) := by ring
      _ ≤ k * m * (2 * (k * m) + 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith
end ClauseBound.Alg.End
