-- Prove2me | solution 1 for CloudAlloc.MWU.scaled_allocation_work
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:50:05.799408+00:00
-- url     : https://prove2.me/submissions/22d5cca8-ea33-4470-a2bd-020a260e0916

import Mathlib
import Definitions.Def_CloudAlloc_MWU_userWork

namespace Aux_CAMsaw

open CloudAlloc.MWU

theorem decomp {N : ℕ} (h L : ℕ → Fin N → ℝ) (i : Fin N) (t : ℕ) :
    userWork h L i t + queue h L t i = ∑ τ ∈ Finset.range t, L τ i := by
  induction t with
  | zero => simp [userWork, queue]
  | succ t ih =>
    have hq : queue h L (t + 1) i = max 0 (L t i + queue h L t i - h t i) := rfl
    have hw : work h L t i = min (h t i) (L t i + queue h L t i) := rfl
    simp only [userWork] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hq, hw, ← ih]
    rcases le_total (h t i) (L t i + queue h L t i) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h1, max_eq_left (by linarith)]; ring

theorem bound {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) (hs : ℕ → Fin N → ℝ) (i : Fin N) (t : ℕ) :
    queue (fun τ j => c * hs τ j) L t i ≤
      (1 - c) * ∑ τ ∈ Finset.range t, L τ i + c * queue hs L t i := by
  induction t with
  | zero => simp [queue]
  | succ t ih =>
    have hA : 0 ≤ ∑ τ ∈ Finset.range t, L τ i := Finset.sum_nonneg (fun τ _ => hL τ i)
    have e1 : queue (fun τ j => c * hs τ j) L (t + 1) i =
        max 0 (L t i + queue (fun τ j => c * hs τ j) L t i - c * hs t i) := rfl
    have e2 : queue hs L (t + 1) i = max 0 (L t i + queue hs L t i - hs t i) := rfl
    rw [e1, e2, Finset.sum_range_succ]
    have hM0 := le_max_left 0 (L t i + queue hs L t i - hs t i)
    have hM1 := le_max_right 0 (L t i + queue hs L t i - hs t i)
    have hLt := hL t i
    apply max_le
    · exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hc0 hM0)
    · have := mul_le_mul_of_nonneg_left hM1 hc0
      nlinarith

end Aux_CAMsaw

open CloudAlloc.MWU Aux_CAMsaw in
theorem solution {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {hs : ℕ → Fin N → ℝ}
    (hhs : ∀ t i, 0 ≤ hs t i) (i : Fin N) (t : ℕ) :
    c * userWork hs L i t ≤ userWork (fun τ j => c * hs τ j) L i t := by
  have d1 := decomp hs L i t
  have d2 := decomp (fun τ j => c * hs τ j) L i t
  have b := bound hc0 hc1 hL hs i t
  nlinarith
