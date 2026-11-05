-- Prove2me | solution 1 for ClauseBound.Boson.Basic.nop_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:41:21.526289+00:00
-- url     : https://prove2.me/submissions/5a6d9b24-7f7f-48c3-b976-8b86ad681461

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
open ClauseBound.Boson.Basic
namespace ClauseBound.Boson.Basic
theorem _root_.solution {n : ℕ} {F : ℤ → Ker} {r : ℤ} {π σ : Multiset ℕ} (h : nop n F r π σ ≠ 0) :
    (∃ l ∈ π, F (r - l) (π.erase l) σ ≠ 0) ∨ ∃ k ∈ σ, F (r + k) π (σ.erase k) ≠ 0 := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 : ∀ l ∈ π, F (r - l) (π.erase l) σ = 0 := fun l hl => by
    by_contra h0
    exact hcon.1 ⟨l, hl, h0⟩
  have h2 : ∀ k ∈ σ, F (r + k) π (σ.erase k) = 0 := fun k hk => by
    by_contra h0
    exact hcon.2 ⟨k, hk, h0⟩
  apply h
  unfold nop
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro k hk
    simp [ann, h2 k (Multiset.mem_toFinset.1 hk)]
  · intro l hl
    have hl' := Multiset.mem_toFinset.1 hl
    simp [cre, hl', h1 l hl']
end ClauseBound.Boson.Basic
