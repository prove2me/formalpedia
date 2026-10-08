-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.next_smallest_value
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:47:06.077567+00:00
-- url     : https://prove2.me/submissions/77f71e6a-9e85-4464-a73e-72edeb17e2b5

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

set_option autoImplicit false

open FedergruenZhengRQ.OPT in
lemma fz9f_anti_left (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    ∀ s t : ℤ, s ≤ t → t ≤ y₁ → G t ≤ G s := by
  obtain ⟨m, hA, hM⟩ := hG
  intro s t hst hty
  by_cases htm : t ≤ m
  · exact hA (Set.mem_Iic.2 (le_trans hst htm)) (Set.mem_Iic.2 htm) hst
  · rw [not_le] at htm
    have h1 : G t ≤ G y₁ :=
      hM (Set.mem_Ici.2 htm.le) (Set.mem_Ici.2 (le_trans htm.le hty)) hty
    exact le_trans h1 (hy₁ s)

open FedergruenZhengRQ.OPT in
lemma fz9f_mono_right (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    ∀ s t : ℤ, y₁ ≤ s → s ≤ t → G s ≤ G t := by
  obtain ⟨m, hA, hM⟩ := hG
  intro s t hys hst
  by_cases hms : m ≤ s
  · exact hM (Set.mem_Ici.2 hms) (Set.mem_Ici.2 (le_trans hms hst)) hst
  · rw [not_le] at hms
    have h1 : G s ≤ G y₁ :=
      hA (Set.mem_Iic.2 (le_trans hys hms.le)) (Set.mem_Iic.2 hms.le) hys
    exact le_trans h1 (hy₁ t)

open FedergruenZhengRQ.OPT in
lemma fz9f_window_bounds (G : ℤ → ℝ) (y₁ : ℤ) :
    ∀ n : ℕ, (window G y₁ n).1 ≤ y₁ ∧ y₁ ≤ (window G y₁ n).2 := by
  intro n
  induction n with
  | zero => simp [window]
  | succ n ih =>
    rw [window]
    split_ifs <;> refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

open FedergruenZhengRQ.OPT in
lemma fz9f_window_step (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    (window G y₁ (n + 1)).1 ≤ (window G y₁ n).1 ∧ (window G y₁ n).2 ≤ (window G y₁ (n + 1)).2 := by
  rw [window]
  split_ifs <;> refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

open FedergruenZhengRQ.OPT in
lemma fz9f_y_succ (G : ℤ → ℝ) (y₁ : ℤ) (k : ℕ) :
    y G y₁ (k + 2) =
      if G ((window G y₁ k).1 - 1) ≤ G ((window G y₁ k).2 + 1) then (window G y₁ k).1 - 1
      else (window G y₁ k).2 + 1 := by
  simp only [y, L, R, Nat.add_sub_cancel]

open FedergruenZhengRQ.OPT in
lemma fz9f_low (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (k : ℕ) :
    ∀ t : ℤ, t ∉ Finset.Icc (window G y₁ k).1 (window G y₁ k).2 → G (y G y₁ (k + 2)) ≤ G t := by
  intro t ht
  rw [Finset.mem_Icc] at ht
  obtain ⟨hb1, hb2⟩ := fz9f_window_bounds G y₁ k
  have hL : t < (window G y₁ k).1 → G ((window G y₁ k).1 - 1) ≤ G t := fun h =>
    fz9f_anti_left G hG y₁ hy₁ t _ (by omega) (by omega)
  have hR : (window G y₁ k).2 < t → G ((window G y₁ k).2 + 1) ≤ G t := fun h =>
    fz9f_mono_right G hG y₁ hy₁ _ t (by omega) (by omega)
  rw [fz9f_y_succ]
  split_ifs with h
  · by_cases h1 : t < (window G y₁ k).1
    · exact hL h1
    · exact le_trans h (hR (by omega))
  · rw [not_le] at h
    by_cases h1 : t < (window G y₁ k).1
    · exact le_trans h.le (hL h1)
    · exact hR (by omega)

open FedergruenZhengRQ.OPT in
theorem solution (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ (Q + 1)) ≤ G t) ∧
    G (y G y₁ Q) ≤ G (y G y₁ (Q + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
  have hLk : L G y₁ (k + 1) = (window G y₁ k).1 := by simp [L]
  have hRk : R G y₁ (k + 1) = (window G y₁ k).2 := by simp [R]
  refine ⟨?_, ?_⟩
  · rw [hLk, hRk]
    exact fz9f_low G hG y₁ hy₁ k
  · rcases k with _ | j
    · show G (y G y₁ 1) ≤ _
      exact hy₁ _
    · apply fz9f_low G hG y₁ hy₁ j
      rw [Finset.mem_Icc]
      obtain ⟨h1, h2⟩ := fz9f_window_step G y₁ j
      have hy := fz9f_y_succ G y₁ (j + 1)
      show ¬ ((window G y₁ j).1 ≤ y G y₁ (j + 1 + 2) ∧ y G y₁ (j + 1 + 2) ≤ (window G y₁ j).2)
      rw [hy]
      split_ifs <;> omega
