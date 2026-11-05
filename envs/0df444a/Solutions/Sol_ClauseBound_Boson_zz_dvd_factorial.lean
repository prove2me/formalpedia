-- Prove2me | solution 1 for ClauseBound.Boson.zz_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:27.716323+00:00
-- url     : https://prove2.me/submissions/24768a9a-06fa-4aa3-8e08-7ba5af044a23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
import Theorems.Thm_ClauseBound_Boson_Dual_pow_mul_factorial_dvd

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution {h : ℕ} (q : Nat.Partition h) : zz q.parts ∣ h.factorial := by
  have h1 : h = ∑ k ∈ q.parts.toFinset, q.parts.count k * k := by
    have := Finset.sum_multiset_count q.parts
    rw [q.parts_sum] at this
    simpa only [smul_eq_mul] using this
  have h2 := Nat.prod_factorial_dvd_factorial_sum q.parts.toFinset fun k => q.parts.count k * k
  rw [← h1] at h2
  exact (prod_dvd_prod_of_dvd _ _ fun k hk => Dual.pow_mul_factorial_dvd (q.parts_pos (Multiset.mem_toFinset.1 hk)) _).trans h2
end ClauseBound.Boson
