-- Prove2me | solution 1 for ClauseBound.Boson.abs_op_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:49.544935+00:00
-- url     : https://prove2.me/submissions/13f0c505-3e55-40a2-b66e-0cf4eda66c1a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
import Theorems.Thm_ClauseBound_Boson_Size_abs_nop_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution {W : ℕ} (hW : 1 ≤ W) (a : List ℕ) (ha : ∀ n ∈ a, n ≤ W) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |op a r π σ| ≤ 2 ^ ((4 * W + 1) * a.length) := by
  induction a generalizing r π σ with
  | nil =>
    rw [List.length_nil, Nat.mul_zero, pow_zero, op]
    split_ifs
    · unfold one
      split_ifs <;> simp
    · simp
  | cons n a ih =>
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm, pow_add, op]
    exact Size.abs_nop_le hW (ha n List.mem_cons_self) (by positivity)
      (fun r π σ hπ hσ => ih (fun m hm => ha m (List.mem_cons_of_mem _ hm)) r hπ hσ) r hπ hσ
end ClauseBound.Boson
