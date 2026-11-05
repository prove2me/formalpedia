-- Prove2me | solution 1 for ClauseBound.TopN.last_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:28.498904+00:00
-- url     : https://prove2.me/submissions/9d0db468-f987-4268-843f-29b56a0d8a49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)
namespace ClauseBound.TopN
theorem _root_.solution (β : ℕ) {n : ℕ} (hn : 6 ≤ n) : 2 ^ (2 * β + 4) * (2 ^ β * n) + 5 * 3 ^ (2 * β + 4) ≤ 3 ^ (2 * β + 4) * (n + 2) := by
  obtain ⟨h, hh⟩ : ∃ h, h = β + 2 := ⟨_, rfl⟩
  have e : 2 * β + 4 = 2 * h := by omega
  have e2 : (2 : ℕ) ^ (2 * h) = 4 ^ h := by rw [pow_mul]; norm_num
  have e3 : (3 : ℕ) ^ (2 * h) = 9 ^ h := by rw [pow_mul]; norm_num
  have h2 : 2 * 2 ^ β ≤ 2 ^ h := by rw [hh, pow_add]; omega
  have h3 : 4 ^ h * 2 ^ h ≤ 9 ^ h := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) h
  have h4 : 2 * (4 ^ h * 2 ^ β) ≤ 9 ^ h := by
    calc 2 * (4 ^ h * 2 ^ β) = 4 ^ h * (2 * 2 ^ β) := by ring
      _ ≤ 4 ^ h * 2 ^ h := Nat.mul_le_mul_left _ h2
      _ ≤ 9 ^ h := h3
  rw [e, e2, e3]
  obtain ⟨A, hA⟩ : ∃ A, A = 9 ^ h := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 4 ^ h * 2 ^ β := ⟨_, rfl⟩
  have e4 : 4 ^ h * (2 ^ β * n) = D * n := by rw [hD]; ring
  rw [e4, ← hA]
  rw [← hD, ← hA] at h4
  nlinarith
end ClauseBound.TopN
