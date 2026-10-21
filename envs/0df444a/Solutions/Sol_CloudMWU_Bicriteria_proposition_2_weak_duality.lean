-- Prove2me | solution 1 for CloudMWU.Bicriteria.proposition_2_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:38:32.207985+00:00
-- url     : https://prove2.me/submissions/54cf5211-b711-48d1-bf87-862cfe494c59

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

open Finset CloudMWU.Bicriteria

theorem solution (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (hstar : ℕ → Fin N → ℝ) (hstar_alloc : IsAllocSeq (1 - ε) hstar)
    (s t : ℕ) (hst : s ≤ t) :
    totalWork hstar L t ≤ totalLoad L s + (1 - ε) * ((t : ℝ) - (s : ℝ)) := by
  -- queue is nonnegative and work ≤ load + queue telescopes
  have hcons : ∀ (a ℓ : ℕ → ℝ) (u : ℕ), cumWork a ℓ u = cumLoad ℓ u - queue a ℓ u := by
    intro a ℓ u
    induction u with
    | zero => simp [cumWork, cumLoad, queue]
    | succ u ih =>
      have hw : work a ℓ u = ℓ u + queue a ℓ u - queue a ℓ (u + 1) := by
        simp only [work, queue]
        rcases le_total (a u) (ℓ u + queue a ℓ u) with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
      unfold cumWork cumLoad at *
      rw [sum_range_succ, sum_range_succ, ih, hw]; ring
  have hq0 : ∀ (a ℓ : ℕ → ℝ) (u : ℕ), 0 ≤ queue a ℓ u := by
    intro a ℓ u; cases u with
    | zero => simp [queue]
    | succ u => simp only [queue]; exact le_max_left _ _
  have hsplit : ∀ i : Fin N,
      cumWork (fun τ => hstar τ i) (fun τ => L τ i) t
        ≤ cumLoad (fun τ => L τ i) s + ∑ τ ∈ Ico s t, hstar τ i := by
    intro i
    have h1 : cumWork (fun τ => hstar τ i) (fun τ => L τ i) t
        = cumWork (fun τ => hstar τ i) (fun τ => L τ i) s
          + ∑ τ ∈ Ico s t, work (fun τ => hstar τ i) (fun τ => L τ i) τ := by
      unfold cumWork
      rw [← Finset.sum_range_add_sum_Ico _ hst]
    have h2 : cumWork (fun τ => hstar τ i) (fun τ => L τ i) s ≤ cumLoad (fun τ => L τ i) s := by
      rw [hcons]; linarith [hq0 (fun τ => hstar τ i) (fun τ => L τ i) s]
    have h3 : ∑ τ ∈ Ico s t, work (fun τ => hstar τ i) (fun τ => L τ i) τ
        ≤ ∑ τ ∈ Ico s t, hstar τ i :=
      Finset.sum_le_sum (fun τ _ => min_le_left _ _)
    linarith
  unfold totalWork totalLoad
  calc ∑ i, cumWork (fun τ => hstar τ i) (fun τ => L τ i) t
      ≤ ∑ i, (cumLoad (fun τ => L τ i) s + ∑ τ ∈ Ico s t, hstar τ i) :=
        Finset.sum_le_sum (fun i _ => hsplit i)
    _ = ∑ i, cumLoad (fun τ => L τ i) s + ∑ τ ∈ Ico s t, ∑ i, hstar τ i := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ i, cumLoad (fun τ => L τ i) s + ∑ τ ∈ Ico s t, (1 - ε) := by
        gcongr with τ _
        exact (hstar_alloc τ).2
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hst]; ring
