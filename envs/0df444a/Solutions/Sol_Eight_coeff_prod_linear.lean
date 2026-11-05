-- Prove2me | solution 1 for Eight.coeff_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:23.25682+00:00
-- url     : https://prove2.me/submissions/8a806444-0522-4638-ab37-af5cba266807

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_prod_linear_eq_sum

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (S : Finset ℕ) (r c : ℕ → ℤ) (i : ℕ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).coeff i = ∑ Q ∈ S.powersetCard i, ∏ s ∈ S, if s ∈ Q then c s else r s := by
  rw [prod_linear_eq_sum, finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun Q _ => ?_
  rw [coeff_C_mul_X_pow]
  simp only [eq_comm]
end Eight
