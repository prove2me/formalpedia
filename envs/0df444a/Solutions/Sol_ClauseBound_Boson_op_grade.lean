-- Prove2me | solution 1 for ClauseBound.Boson.op_grade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:44:26.471427+00:00
-- url     : https://prove2.me/submissions/0d955efd-dd67-489c-83e5-20ea7b59c655

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
import Theorems.Thm_ClauseBound_Boson_Basic_nop_ne_zero
import Theorems.Thm_ClauseBound_Boson_Basic_sum_erase_cast

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic
namespace ClauseBound.Boson
theorem _root_.solution {a : List ℕ} {r : ℤ} {π σ : Multiset ℕ} (h : op a r π σ ≠ 0) : (π.sum : ℤ) = σ.sum + r := by
  induction a generalizing r π σ with
  | nil =>
    unfold op at h
    split_ifs at h with h0
    · unfold one at h
      split_ifs at h with h1
      · rw [h0, h1, add_zero]
      · exact absurd rfl h
    · exact absurd rfl h
  | cons n a ih =>
    rcases nop_ne_zero (show nop n (op a) r π σ ≠ 0 from h) with ⟨l, hl, h1⟩ | ⟨k, hk, h1⟩
    · have := ih h1
      rw [sum_erase_cast hl] at this
      omega
    · have := ih h1
      rw [sum_erase_cast hk] at this
      omega
end ClauseBound.Boson
