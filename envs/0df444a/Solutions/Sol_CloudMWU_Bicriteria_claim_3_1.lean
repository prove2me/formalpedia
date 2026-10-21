-- Prove2me | solution 1 for CloudMWU.Bicriteria.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:42:58.935596+00:00
-- url     : https://prove2.me/submissions/716b9cde-fbf6-436a-a6ff-d222b537b296

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

open Finset CloudMWU.Bicriteria

theorem cloudmwu_c31_cons (a ℓ : ℕ → ℝ) (u : ℕ) :
    cumWork a ℓ u = cumLoad ℓ u - queue a ℓ u := by
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

theorem cloudmwu_c31_q0 (a ℓ : ℕ → ℝ) (u : ℕ) : 0 ≤ queue a ℓ u := by
  cases u with
  | zero => simp [queue]
  | succ u => simp only [queue]; exact le_max_left _ _

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (r m : ℕ)
    (hfail : totalWork h L (r + m) < totalLoad L r) :
    ∃ i : Fin N, ∀ r' ∈ Icc r (r + m), 0 < runQueue h L r' i := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- allocations are positive
  have hsimp : ∀ t, h t ∈ truncSimplex N ε := by
    intro t
    cases t with
    | zero => exact hrun.1
    | succ t => exact (hrun.2 t).2.1
  have hpos : ∀ t i, 0 ≤ h t i := by
    intro t i
    have := (hsimp t).2 i
    have : 0 ≤ ε / (N : ℝ) := by positivity
    linarith
  by_contra hcon
  push_neg at hcon
  have key : ∀ i : Fin N, cumLoad (fun τ => L τ i) r
      ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) (r + m) := by
    intro i
    obtain ⟨r', hr', hq⟩ := hcon i
    rw [Finset.mem_Icc] at hr'
    have hq0 : queue (fun τ => h τ i) (fun τ => L τ i) r' = 0 :=
      le_antisymm hq (cloudmwu_c31_q0 _ _ _)
    have h1 : cumLoad (fun τ => L τ i) r ≤ cumLoad (fun τ => L τ i) r' := by
      unfold cumLoad
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hr'.1)
        (fun τ _ _ => hL τ i)
    have h2 : cumWork (fun τ => h τ i) (fun τ => L τ i) r'
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) (r + m) := by
      unfold cumWork
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hr'.2)
      intro τ _ _
      unfold work
      exact le_min (hpos τ i) (add_nonneg (hL τ i) (cloudmwu_c31_q0 _ _ _))
    rw [cloudmwu_c31_cons _ _ r', hq0] at h2
    linarith
  have : totalLoad L r ≤ totalWork h L (r + m) := by
    unfold totalLoad totalWork
    exact Finset.sum_le_sum (fun i _ => key i)
  linarith
