-- Prove2me | solution 2 for CloudMWU.Bicriteria.scaling_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:17:45.361253+00:00
-- url     : https://prove2.me/submissions/582e7cd4-be97-451d-b666-b00ba7070cac

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

set_option autoImplicit false
open Finset CloudMWU.Bicriteria

lemma queue_nonneg (a ℓ : ℕ → ℝ) (t : ℕ) : 0 ≤ queue a ℓ t := by
  cases t with
  | zero => simp [queue]
  | succ t => simp [queue]

lemma queue_succ_eq (a ℓ : ℕ → ℝ) (t : ℕ) :
    queue a ℓ (t + 1) = ℓ t + queue a ℓ t - work a ℓ t := by
  simp only [queue, work]
  rcases le_total (a t) (ℓ t + queue a ℓ t) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

lemma cumWork_eq (a ℓ : ℕ → ℝ) (t : ℕ) :
    cumWork a ℓ t = cumLoad ℓ t - queue a ℓ t := by
  induction t with
  | zero => simp [cumWork, cumLoad, queue]
  | succ t ih =>
    have h1 : cumWork a ℓ (t + 1) = cumWork a ℓ t + work a ℓ t := by
      simp [cumWork, Finset.sum_range_succ]
    have h2 : cumLoad ℓ (t + 1) = cumLoad ℓ t + ℓ t := by
      simp [cumLoad, Finset.sum_range_succ]
    rw [h1, h2, ih, queue_succ_eq]; ring

lemma work_le (a ℓ : ℕ → ℝ) (t : ℕ) : work a ℓ t ≤ a t := min_le_left _ _

lemma queue_anti (a b ℓ : ℕ → ℝ) (hab : ∀ τ, a τ ≤ b τ) (t : ℕ) :
    queue b ℓ t ≤ queue a ℓ t := by
  induction t with
  | zero => simp [queue]
  | succ t ih =>
    simp only [queue]
    exact max_le_max le_rfl (by linarith [hab t])

lemma queue_scale (ℓ : ℕ → ℝ) (hℓ : ∀ t, 0 ≤ ℓ t) (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1)
    (a : ℕ → ℝ) (t : ℕ) :
    queue (fun τ => κ * a τ) ℓ t ≤ (1 - κ) * cumLoad ℓ t + κ * queue a ℓ t := by
  induction t with
  | zero => simp [queue, cumLoad]
  | succ t ih =>
    have hΛ : 0 ≤ cumLoad ℓ t := Finset.sum_nonneg (fun τ _ => hℓ τ)
    have h2 : cumLoad ℓ (t + 1) = cumLoad ℓ t + ℓ t := by
      simp [cumLoad, Finset.sum_range_succ]
    have hk : 0 ≤ 1 - κ := by linarith
    have hmul : 0 ≤ (1 - κ) * cumLoad ℓ t := mul_nonneg hk hΛ
    have hmul2 : 0 ≤ (1 - κ) * ℓ t := mul_nonneg hk (hℓ t)
    simp only [queue]
    rw [h2]
    refine max_le ?_ ?_
    · have : 0 ≤ κ * max 0 (ℓ t + queue a ℓ t - a t) := mul_nonneg h0 (le_max_left _ _)
      nlinarith
    · have hm : κ * (ℓ t + queue a ℓ t - a t) ≤ κ * max 0 (ℓ t + queue a ℓ t - a t) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) h0
      nlinarith [mul_le_mul_of_nonneg_left ih h0]

theorem solution (ℓ : ℕ → ℝ) (hℓ : ∀ t, 0 ≤ ℓ t) :
    (∀ (κ : ℝ), 0 ≤ κ → κ ≤ 1 → ∀ (a : ℕ → ℝ) (t : ℕ),
      κ * cumWork a ℓ t ≤ cumWork (fun τ => κ * a τ) ℓ t) ∧
    (∀ (a b : ℕ → ℝ), (∀ τ, a τ ≤ b τ) → ∀ t : ℕ, cumWork a ℓ t ≤ cumWork b ℓ t) := by
  refine ⟨fun κ h0 h1 a t => ?_, fun a b hab t => ?_⟩
  · rw [cumWork_eq, cumWork_eq]
    have := queue_scale ℓ hℓ κ h0 h1 a t
    nlinarith
  · rw [cumWork_eq, cumWork_eq]
    have := queue_anti a b ℓ hab t
    linarith
