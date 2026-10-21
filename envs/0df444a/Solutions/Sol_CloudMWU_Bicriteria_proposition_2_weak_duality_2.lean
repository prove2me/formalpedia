-- Prove2me | solution 2 for CloudMWU.Bicriteria.proposition_2_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:17:46.704279+00:00
-- url     : https://prove2.me/submissions/423cd92e-4ff7-4601-a7e5-9a2726e0d0fd

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

theorem solution (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (hstar : ℕ → Fin N → ℝ) (hstar_alloc : IsAllocSeq (1 - ε) hstar)
    (s t : ℕ) (hst : s ≤ t) :
    totalWork hstar L t ≤ totalLoad L s + (1 - ε) * ((t : ℝ) - (s : ℝ)) := by
  have hper : ∀ i, cumWork (fun τ => hstar τ i) (fun τ => L τ i) t ≤
      cumLoad (fun τ => L τ i) s + ∑ τ ∈ Finset.Ico s t, hstar τ i := by
    intro i
    have h1 : cumWork (fun τ => hstar τ i) (fun τ => L τ i) t =
        cumWork (fun τ => hstar τ i) (fun τ => L τ i) s +
          ∑ τ ∈ Finset.Ico s t, work (fun τ => hstar τ i) (fun τ => L τ i) τ := by
      unfold cumWork
      rw [Finset.sum_range_add_sum_Ico _ hst]
    have h2 : cumWork (fun τ => hstar τ i) (fun τ => L τ i) s ≤
        cumLoad (fun τ => L τ i) s := by
      rw [cumWork_eq]; linarith [queue_nonneg (fun τ => hstar τ i) (fun τ => L τ i) s]
    have h3 : ∑ τ ∈ Finset.Ico s t, work (fun τ => hstar τ i) (fun τ => L τ i) τ ≤
        ∑ τ ∈ Finset.Ico s t, hstar τ i :=
      Finset.sum_le_sum (fun τ _ => work_le (fun τ => hstar τ i) (fun τ => L τ i) τ)
    linarith
  unfold totalWork totalLoad
  calc ∑ i, cumWork (fun τ => hstar τ i) (fun τ => L τ i) t
      ≤ ∑ i, (cumLoad (fun τ => L τ i) s + ∑ τ ∈ Finset.Ico s t, hstar τ i) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = ∑ i, cumLoad (fun τ => L τ i) s + ∑ τ ∈ Finset.Ico s t, ∑ i, hstar τ i := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ i, cumLoad (fun τ => L τ i) s + ∑ τ ∈ Finset.Ico s t, (1 - ε) := by
        gcongr with τ hτ
        exact (hstar_alloc τ).2
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hst]; ring
