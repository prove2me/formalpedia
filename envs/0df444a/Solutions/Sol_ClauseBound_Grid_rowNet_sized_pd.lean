-- Prove2me | solution 1 for ClauseBound.Grid.rowNet_sized_pd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:47.906188+00:00
-- url     : https://prove2.me/submissions/7d430b54-0bb8-48e7-9c11-be137cdb5a8d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_abs_boole_le
import Theorems.Thm_ClauseBound_Grid_abs_mul_prod_le
import Theorems.Thm_ClauseBound_Grid_card_lt_le
import Theorems.Thm_ClauseBound_Grid_rowNet_shaped_pd
import Theorems.Thm_P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {p d L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (p * d ^ 2 * L)) (d * B + d ^ 2 * b) where
  toShaped := rowNet_shaped_pd hm hρ hγ hα R C t₀ hcard hcap
  abs_W a z := by
    simp only [rowNet, rowW]
    rw [mul_comm]
    refine abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hR _ _) ?_
    rw [Finset.card_univ, hγ]
    exact Nat.le_add_right _ _
  abs_f a c z θ := by
    have hn : #(univ.filter fun k : γ × γ => k.1 < k.2) * b ≤ d * B + d ^ 2 * b :=
      (Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans (Nat.le_add_left _ _)
    simp only [rowNet]
    split_ifs
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => htop _ _ _ _) hn
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hbot _ _ _ _) hn
  abs_Ψ a c z z' hac := by
    rcases lt_or_gt_of_ne hac with h | h
    · exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z z'
    · rw [Network.Ψ_comm]
      exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z' z
end ClauseBound.Grid
