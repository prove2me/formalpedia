-- Prove2me | solution 1 for CloudMWU.Bicriteria.scaling_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:38:31.405482+00:00
-- url     : https://prove2.me/submissions/b0286aed-a8d7-478a-a41b-0d632bfbd738

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

open Finset CloudMWU.Bicriteria

/-- conservation: cumulative work = cumulative load − current queue. -/
theorem cloudmwu_cumWork_eq (a ℓ : ℕ → ℝ) (t : ℕ) :
    cumWork a ℓ t = cumLoad ℓ t - queue a ℓ t := by
  induction t with
  | zero => simp [cumWork, cumLoad, queue]
  | succ t ih =>
    have hw : work a ℓ t = ℓ t + queue a ℓ t - queue a ℓ (t + 1) := by
      simp only [work, queue]
      rcases le_total (a t) (ℓ t + queue a ℓ t) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    unfold cumWork cumLoad at *
    rw [sum_range_succ, sum_range_succ, ih, hw]; ring

theorem solution (ℓ : ℕ → ℝ) (hℓ : ∀ t, 0 ≤ ℓ t) :
    (∀ (κ : ℝ), 0 ≤ κ → κ ≤ 1 → ∀ (a : ℕ → ℝ) (t : ℕ),
      κ * cumWork a ℓ t ≤ cumWork (fun τ => κ * a τ) ℓ t) ∧
    (∀ (a b : ℕ → ℝ), (∀ τ, a τ ≤ b τ) → ∀ t : ℕ, cumWork a ℓ t ≤ cumWork b ℓ t) := by
  have hC : ∀ t, 0 ≤ cumLoad ℓ t := fun t =>
    Finset.sum_nonneg (fun τ _ => hℓ τ)
  constructor
  · intro κ hκ0 hκ1 a t
    -- key: Q_{κa}(t) ≤ (1-κ) C_t + κ Q_a(t)
    have key : ∀ t, queue (fun τ => κ * a τ) ℓ t ≤ (1 - κ) * cumLoad ℓ t + κ * queue a ℓ t := by
      intro t
      induction t with
      | zero => simp [queue, cumLoad]
      | succ t ih =>
        have hCs : cumLoad ℓ (t + 1) = cumLoad ℓ t + ℓ t := by
          simp [cumLoad, sum_range_succ]
        simp only [queue]
        rw [hCs]
        have hq0 : 0 ≤ max 0 (ℓ t + queue a ℓ t - a t) := le_max_left _ _
        have hq1 : ℓ t + queue a ℓ t - a t ≤ max 0 (ℓ t + queue a ℓ t - a t) := le_max_right _ _
        have hCt := hC t
        have hlt := hℓ t
        apply max_le
        · nlinarith
        · nlinarith
    rw [cloudmwu_cumWork_eq, cloudmwu_cumWork_eq]
    have := key t
    nlinarith
  · intro a b hab t
    have key : ∀ t, queue b ℓ t ≤ queue a ℓ t := by
      intro t
      induction t with
      | zero => simp [queue]
      | succ t ih =>
        simp only [queue]
        exact max_le_max le_rfl (by linarith [hab t])
    rw [cloudmwu_cumWork_eq, cloudmwu_cumWork_eq]
    linarith [key t]
