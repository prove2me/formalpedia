-- Prove2me | solution 1 for ClauseBound.Grid.ZG_cross_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:47.313245+00:00
-- url     : https://prove2.me/submissions/0b2ec6d2-0817-4ad9-8301-e36bcd4e0454

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
import Theorems.Thm_P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2
import Theorems.Thm_Groundwork_sum_tuples_prod


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {κ : Type} [DecidableEq κ] (R : Inst (ρ × γ) α) (I : Finset κ) (i₀ : κ)
    (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * ZG R (fun _ => Cross.X) = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG R fun ω => A (f ω) := by
  unfold ZG
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← mul_sum, ← mul_sum]
  have h1 := sum_tuples_prod (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀ fun ω i => app (A i) ℓ ω
  rw [filter_mem_Ω] at h1
  have h2 : ∏ ω ∈ Ω ρ γ, ∑ i ∈ I, app (A i) ℓ ω = d ^ #(Ω ρ γ) * ∏ ω ∈ Ω ρ γ, app Cross.X ℓ ω := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun ω _ => h _ _ _ _
  rw [h1, h2]
  ring
end ClauseBound.Grid
