-- Prove2me | solution 1 for ClauseBound.Boson.Final.big_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:21.825626+00:00
-- url     : https://prove2.me/submissions/5f4124f6-5d5d-4ad3-b121-1b139199e4d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final
namespace ClauseBound.Boson.Final
theorem _root_.solution {c₀ c₁ c₂ lam h : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hS : ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ 2 ^ (c₂ * lam)) :
    big h ≤ (2 * lam) ^ (c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂)) := by
  have h0 : Nat.clog 2 (∑ E ∈ range (4 * h + 1), Partitions.p E) ≤ c₂ * lam := (Nat.clog_le_iff_le_pow (by norm_num)).2 hS
  have h1 : (h + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * lam ^ 4 := by
    have : h + 1 ≤ (c₀ + 1) * lam ^ 2 := by
      have : 1 ≤ lam ^ 2 := Nat.one_le_pow _ _ hl
      rw [Nat.add_mul, Nat.one_mul]
      omega
    calc (h + 1) ^ 2 ≤ ((c₀ + 1) * lam ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = (c₀ + 1) ^ 2 * lam ^ 4 := by ring
  have h2 : c₂ * lam ≤ c₂ * lam ^ 4 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) lam)
  have h3 : (40 * (c₀ + 1) ^ 2 + c₂) * lam ^ 4 ≤ (2 * lam) ^ (c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂)) := by
    generalize 40 * (c₀ + 1) ^ 2 + c₂ = A
    have e1 : 1 ≤ (2 * lam) ^ c₁ := Nat.one_le_pow _ _ (by omega)
    have e2 : lam ^ 4 ≤ (2 * lam) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e3 : A ≤ (2 * lam) ^ A := (Nat.lt_two_pow_self (n := A)).le.trans (Nat.pow_le_pow_left (by omega) A)
    calc A * lam ^ 4 = 1 * lam ^ 4 * A := by ring
      _ ≤ (2 * lam) ^ c₁ * (2 * lam) ^ 4 * (2 * lam) ^ A := Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
      _ = (2 * lam) ^ (c₁ + 4 + A) := by rw [pow_add, pow_add]
  calc big h ≤ 40 * ((c₀ + 1) ^ 2 * lam ^ 4) + c₂ * lam ^ 4 := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (h0.trans h2)
    _ = (40 * (c₀ + 1) ^ 2 + c₂) * lam ^ 4 := by ring
    _ ≤ _ := h3
end ClauseBound.Boson.Final
