-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_first_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:40.12801+00:00
-- url     : https://prove2.me/submissions/096003e9-9aae-41ce-8b2b-3166280a33d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
import Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_add_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_eight_mul_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_two_pow_mul_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (Kup lam B cnt z : ℕ) :
    size (cnt * PaddedDescent.F.instLen Kup lam B + 8 * z + 4 * lam + 40) ≤
      size cnt + size z + (Kup - 1) * lam + size (4 * lam + Kup * (3 * B + 14) + 10) + size (4 * lam + 40) + 4 := by
  have h1 : PaddedDescent.F.instLen Kup lam B ≤ 2 ^ ((Kup - 1) * lam) * (4 * lam + Kup * (3 * B + 14) + 10) := by
    unfold PaddedDescent.F.instLen
    have hE : 1 ≤ 2 ^ ((Kup - 1) * lam) := Nat.one_le_two_pow
    generalize 2 ^ ((Kup - 1) * lam) = E at *
    have e1 : 4 * lam ≤ E * (4 * lam) := Nat.le_mul_of_pos_left _ hE
    have e2 : Kup * 4 ≤ E * (Kup * 4) := Nat.le_mul_of_pos_left _ hE
    have e3 : 10 ≤ E * 10 := Nat.le_mul_of_pos_left _ hE
    calc 4 * lam + Kup * (E * (3 * B + 10) + 4) + 10
        = 4 * lam + (E * (Kup * (3 * B + 10)) + Kup * 4) + 10 := by ring
      _ ≤ E * (4 * lam) + (E * (Kup * (3 * B + 10)) + E * (Kup * 4)) + E * 10 := by gcongr
      _ = E * (4 * lam + Kup * (3 * B + 14) + 10) := by ring
  have h2 : size (PaddedDescent.F.instLen Kup lam B) ≤ (Kup - 1) * lam + 1 + size (4 * lam + Kup * (3 * B + 14) + 10) :=
    (Nat.size_le_size h1).trans (size_two_pow_mul_le _ _)
  have h3 : cnt * PaddedDescent.F.instLen Kup lam B + 8 * z + 4 * lam + 40 =
      cnt * PaddedDescent.F.instLen Kup lam B + (8 * z + (4 * lam + 40)) := by ring
  have h4 := size_add_le (cnt * PaddedDescent.F.instLen Kup lam B) (8 * z + (4 * lam + 40))
  have h5 := size_add_le (8 * z) (4 * lam + 40)
  have h6 := size_mul_le cnt (PaddedDescent.F.instLen Kup lam B)
  have h7 := size_eight_mul_le z
  rw [h3]
  omega
end ClauseBound.Gen.Rate
