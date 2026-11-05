-- Prove2me | solution 1 for ClauseBound.Grid.rowNet_shaped_pd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:45.482411+00:00
-- url     : https://prove2.me/submissions/ff6cc036-83fb-4084-a964-6c4b24bf7dc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_sum_erase_le
import Theorems.Thm_ClauseBound_Grid_card_state_pd
import Theorems.Thm_ClauseBound_Grid_card_labels_le
import Theorems.Thm_ClauseBound_Grid_rowNet_c_le_pd

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {p d L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) :
    (rowNet R C t₀ L).Shaped (m * (p * d ^ 2 * L)) where
  card_S a := by
    simp only [rowNet, Finset.card_univ]
    rw [card_state_pd hρ hγ hα]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  c_symm a b := by simp only [rowNet, min_comm, max_comm]
  sum_c a := by
    refine (sum_erase_le ρ hρ _ (fun b => rowNet_c_le_pd hm hγ R C t₀ hcap a b) a).trans (le_of_eq ?_)
    ring
  card_lab a b hab := by
    simp only [Network.lab, rowNet, if_pos (min_lt_max.2 hab), rowΘ, hγ]
    exact card_labels_le hγ hα _ _ (fun k => hcard _) t₀
end ClauseBound.Grid
