-- Prove2me | solution 1 for ClauseBound.Part.Lower.sum_k_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:34:01.868981+00:00
-- url     : https://prove2.me/submissions/e6019f96-3f5c-47e8-9ca7-6c19d404af3e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_sum_inv_sq_le
import Theorems.Thm_ClauseBound_Part_Lower_le_sum_inv_sq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {K : ℕ} (hK : 1 ≤ K) :
    1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) - K / 4 - 486 * γ / α ^ 4 * (Real.pi ^ 2 / 6)
      ≤ ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
  have e : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      = 1 / α ^ 2 * (1 / (k : ℝ) ^ 2) - 1 / 4 - 486 * γ / α ^ 4 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.1 hk).1
    field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Ioc, nsmul_eq_mul]
  have h1 := le_sum_inv_sq hK
  have h2 := sum_inv_sq_le K
  have h3 : 1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) ≤ 1 / α ^ 2 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by gcongr
  have h4 : 486 * γ / α ^ 4 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 ≤ 486 * γ / α ^ 4 * (Real.pi ^ 2 / 6) := by gcongr
  have h5 : ((K - 0 : ℕ) : ℝ) * (1 / 4) = K / 4 := by simp; ring
  linarith
end ClauseBound.Part.Lower
