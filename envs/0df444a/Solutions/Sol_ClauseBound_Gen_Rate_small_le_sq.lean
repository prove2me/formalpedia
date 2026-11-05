-- Prove2me | solution 1 for ClauseBound.Gen.Rate.small_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:01.297525+00:00
-- url     : https://prove2.me/submissions/060436bb-914a-422f-acee-a2e046fbbcf5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (Kup lam B : ℕ) (hK : 44 ≤ Kup) (hlam : 1 ≤ lam) :
    4 * lam + Kup * (3 * B + 14) + 10 ≤ (Kup * (lam + B)) ^ 2 ∧ 4 * lam + 40 ≤ (Kup * (lam + B)) ^ 2 := by
  have h1 : lam + B ≤ Kup * (lam + B) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : 44 * (lam + B) ≤ Kup * (lam + B) := Nat.mul_le_mul_right _ hK
  generalize hX : Kup * (lam + B) = X at *
  have h3 : 44 * X ≤ X ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  have h4 : Kup * (3 * B + 14) ≤ 14 * X := by
    rw [← hX]
    calc Kup * (3 * B + 14) ≤ Kup * (14 * (lam + B)) := Nat.mul_le_mul_left _ (by omega)
      _ = 14 * (Kup * (lam + B)) := by ring
  constructor <;> omega
end ClauseBound.Gen.Rate
