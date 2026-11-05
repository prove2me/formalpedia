-- Prove2me | solution 1 for ClauseBound.Grid.Z_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:51.780817+00:00
-- url     : https://prove2.me/submissions/afa51f25-ccbe-440e-8389-87d6c8607d3a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
import Theorems.Thm_ClauseBound_Grid_ZG_cross_mul_eq_sum
import Theorems.Thm_Groundwork_Grid_Z_eq_ZG_X


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {J κ : Type} [Fintype J] [LinearOrder J] [DecidableEq κ] (R : Inst J α) (d₀ : α) (e : J ≃ ρ × γ)
    (I : Finset κ) (i₀ : κ) (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * R.Z d₀ = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG (onGrid R d₀ e) fun ω => A (f ω) := by
  rw [Z_eq_ZG_X R d₀ e]
  exact ZG_cross_mul_eq_sum _ I i₀ A d h
end ClauseBound.Grid
