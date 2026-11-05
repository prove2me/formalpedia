-- Prove2me | solution 1 for ClauseBound.Boson.nop_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:42:02.64423+00:00
-- url     : https://prove2.me/submissions/5eecf4b3-e825-4126-93f6-6470645226fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic
namespace ClauseBound.Boson
theorem _root_.solution (n : ℕ) (F : ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) {S T : Finset ℕ} (hS : π.toFinset ⊆ S) (hT : σ.toFinset ⊆ T) :
    nop n F r π σ = ∑ l ∈ S, bet n l * cre l (F (r - l)) π σ + ∑ k ∈ T, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ := by
  unfold nop
  rw [Finset.sum_subset hS, Finset.sum_subset hT]
  · intro k _ hk
    have : σ.count k = 0 := Multiset.count_eq_zero.2 fun h => hk (Multiset.mem_toFinset.2 h)
    simp [ann, this]
  · intro l _ hl
    have : l ∉ π := fun h => hl (Multiset.mem_toFinset.2 h)
    simp [cre, this]
end ClauseBound.Boson
