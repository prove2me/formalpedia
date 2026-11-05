-- Prove2me | solution 1 for ClauseBound.Grid.U_rowNet_pd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:34.877685+00:00
-- url     : https://prove2.me/submissions/bea2d20f-418b-4006-859a-1eeab0d3b44f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_two_mul_pairs
import Theorems.Thm_ClauseBound_Grid_sum_erase_eq
import Theorems.Thm_P2M_Groundwork_Grid___eq_product_67598949e673


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = p * (p - 1) * d * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by
  have hsum : (∑ ω ∈ Ω ρ γ, (C ω).cap) = ∑ p ∈ pairs ρ, ∑ k : γ × γ with k.1 < k.2, (C (p, k)).cap := by
    rw [Ω_eq_product, Finset.sum_product]
  have h := sum_erase_eq (X := ρ) fun q => Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C (q, k)).cap
  rw [Network.U]
  simp only [rowNet]
  rw [h, Finset.sum_add_distrib, ← hsum, Finset.sum_const, smul_eq_mul, mul_add,
    ← mul_assoc, two_mul_pairs, hρ, hγ]
  ring
end ClauseBound.Grid
