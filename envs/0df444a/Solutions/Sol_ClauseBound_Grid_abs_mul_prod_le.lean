-- Prove2me | solution 1 for ClauseBound.Grid.abs_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:37.290261+00:00
-- url     : https://prove2.me/submissions/17b25a84-a61c-4642-a7ba-4ae3a29d0348

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_abs_prod_le_pow
import Theorems.Thm_Groundwork_abs_prod_le_one


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {ι κ : Type} (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b n : ℕ}
    (he : ∀ i, |e i| ≤ 1) (hf : ∀ k, |f k| ≤ 2 ^ b) (hn : #t * b ≤ n) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ n := by
  rw [abs_mul]
  calc |∏ i ∈ s, e i| * |∏ k ∈ t, f k| ≤ 1 * 2 ^ (#t * b) :=
        mul_le_mul (abs_prod_le_one s e he) (abs_prod_le_pow t f b fun k _ => hf k) (abs_nonneg _) zero_le_one
    _ = 2 ^ (#t * b) := one_mul _
    _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
end ClauseBound.Grid
