-- Prove2me | solution 1 for ContJRP.Align.observation_2_2_rep_orders
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:55:27.954467+00:00
-- url     : https://prove2.me/submissions/4272823f-c204-4972-a5c3-b87e7ba669ca

import Mathlib
import Definitions.Def_ContJRP_Align_Policy

set_option autoImplicit false
open ContJRP.Align

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ Δ : ℝ, 0 ≤ Δ → numOrders (active ε Tt Tstar) Rstar Δ ≤ numOrders Finset.univ Tstar Δ := by
  intro Δ _
  unfold numOrders
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_biUnion] at hx ⊢
  obtain ⟨ℓ, hℓ, hx⟩ := hx
  obtain ⟨i, hi, _⟩ := hR ℓ hℓ
  exact ⟨i, Finset.mem_univ i, by rw [← hi]; exact hx⟩
