-- Prove2me | solution 1 for Eight.prod_linear_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:15.693073+00:00
-- url     : https://prove2.me/submissions/dceeb98d-789e-4c62-adad-9023fa89a2fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (S : Finset ℕ) (r c : ℕ → ℤ) :
    ∏ s ∈ S, (C (r s) + X * C (c s)) = ∑ Q ∈ S.powerset, C (∏ s ∈ S, if s ∈ Q then c s else r s) * X ^ #Q := by
  simp_rw [add_comm (C (r _))]
  rw [Finset.prod_add]
  refine sum_congr rfl fun Q hQ => ?_
  have hQ' := mem_powerset.1 hQ
  rw [prod_ite, filter_mem_eq_inter, filter_notMem_eq_sdiff, inter_eq_right.2 hQ', prod_mul_distrib, prod_const, C_mul, map_prod, map_prod]
  ring
end Eight
