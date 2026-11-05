-- Prove2me | solution 1 for Eight.Level.Arith.exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:22.779712+00:00
-- url     : https://prove2.me/submissions/9bafb23a-1e00-48de-9eb8-adcdcad359f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Arith
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Arith

set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork
open Eight.Level.Arith
namespace Eight.Level.Arith
theorem _root_.solution {g K lam : ℕ} {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) :
    e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K
      ≤ 2 * e * (g : ℝ) ^ 4 + ((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hkg : (K : ℝ) ≤ g := by exact_mod_cast hg
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (g : ℝ) ^ 4 * lam / K := ⟨_, rfl⟩
  have hqK : q * K = (g : ℝ) ^ 4 * lam := by rw [hq]; field_simp
  have a1 : (g : ℝ) ^ 3 * lam ≤ q := by
    refine le_of_mul_le_mul_right ?_ hk
    rw [hqK]
    have : (g : ℝ) ^ 3 * lam * K ≤ (g : ℝ) ^ 3 * lam * g := mul_le_mul_of_nonneg_left hkg (by positivity)
    linarith [this]
  have a2 : e * ((g : ℝ) ^ 3 * lam) ≤ e * q := mul_le_mul_of_nonneg_left a1 h0
  have e1 : (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K = (e + 2) * q := by
    rw [hq]; push_cast; ring
  have e2 : ((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ) = e * (rho * ((g : ℝ) ^ 4 * lam)) + (2 * e + 2) * q := by
    rw [hq]; push_cast; ring
  rw [e1, e2]
  linarith
end Eight.Level.Arith
