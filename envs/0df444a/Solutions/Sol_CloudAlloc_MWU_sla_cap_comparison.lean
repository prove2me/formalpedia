-- Prove2me | solution 1 for CloudAlloc.MWU.sla_cap_comparison
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:43:26.962295+00:00
-- url     : https://prove2.me/submissions/406e2aef-ba34-4746-92e5-5658a0c5c2fb

import Mathlib
import Definitions.Def_CloudAlloc_MWU_userWork

namespace Aux_CAMscc

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

theorem mono {N : ℕ} (L : ℕ → Fin N → ℝ) (h1 h2 : ℕ → Fin N → ℝ) (i : Fin N)
    (h : ∀ τ, h1 τ i ≤ h2 τ i) (t : ℕ) : queue h2 L t i ≤ queue h1 L t i := by
  induction t with
  | zero => simp [queue]
  | succ t ih =>
    have e1 : queue h1 L (t + 1) i = max 0 (L t i + queue h1 L t i - h1 t i) := rfl
    have e2 : queue h2 L (t + 1) i = max 0 (L t i + queue h2 L t i - h2 t i) := rfl
    rw [e1, e2]
    exact max_le_max (le_refl 0) (by linarith [h t])

end Aux_CAMscc

open CloudAlloc.MWU Aux_CAMscc in
theorem solution {N : ℕ} {c b : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) (i : Fin N) {h'' h' : ℕ → Fin N → ℝ}
    (hh'' : ∀ τ, 0 ≤ h'' τ i ∧ h'' τ i ≤ b) (hh' : ∀ τ, h' τ i = c * b) :
    ∀ t, c * userWork h'' L i t ≤ userWork h' L i t := by
  intro t
  have d1 := decomp h'' L i t
  have d2 := decomp h' L i t
  have hB : queue (fun _ _ => c * b) L t i ≤
      (1 - c) * ∑ τ ∈ Finset.range t, L τ i + c * queue (fun _ _ => b) L t i :=
    bound hc0 hc1 hL (fun _ _ => b) i t
  have m1 : queue h' L t i ≤ queue (fun _ _ => c * b) L t i :=
    mono L (fun _ _ => c * b) h' i (fun τ => le_of_eq (hh' τ).symm) t
  have m2 : queue (fun _ _ => b) L t i ≤ queue h'' L t i :=
    mono L h'' (fun _ _ => b) i (fun τ => (hh'' τ).2) t
  have hA : 0 ≤ ∑ τ ∈ Finset.range t, L τ i := Finset.sum_nonneg (fun τ _ => hL τ i)
  have m3 := mul_le_mul_of_nonneg_left m2 hc0
  nlinarith
