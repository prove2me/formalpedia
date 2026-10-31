-- Prove2me | solution 1 for DisplayMNL.Rounding.claim_5_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:38:30.305529+00:00
-- url     : https://prove2.me/submissions/fa242b48-b8fd-4e4b-a2d7-5c0d53befbdc

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model
import Theorems.Thm_DisplayMNL_Rounding_revenue_insert

open Finset

namespace RRBC55
open DisplayMNL.Rounding

theorem chain_up (f : ℕ → ℝ) (a c : ℕ) (h : ∀ k, a ≤ k → k < c → f k ≤ f (k + 1)) :
    ∀ k l, a ≤ k → k ≤ l → l ≤ c → f k ≤ f l := by
  intro k l hak hkl hlc
  induction l with
  | zero =>
    have : k = 0 := by omega
    subst this; exact le_rfl
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hkl with h1 | h1
    · rw [h1]
    · exact (ih (by omega) (by omega)).trans (h l (by omega) (by omega))

theorem chain_down (f : ℕ → ℝ) (a c : ℕ) (h : ∀ k, a ≤ k → k < c → f (k + 1) ≤ f k) :
    ∀ k l, a ≤ k → k ≤ l → l ≤ c → f l ≤ f k := by
  have := chain_up (fun k => - f k) a c (fun k h1 h2 => by simp only [neg_le_neg_iff]; exact h k h1 h2)
  intro k l h1 h2 h3
  have := this k l h1 h2 h3
  simpa using this

/-- Abstract unimodality: a sequence updated by convex combinations with non-increasing
targets is unimodal. -/
theorem abstract_unimodal (f x : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ k, a ≤ k → k < b → ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ f (k + 1) = f k * θ + x k * (1 - θ))
    (hx : ∀ k, a ≤ k → k + 1 < b → x (k + 1) ≤ x k) :
    IsUnimodalOn f a b := by
  classical
  have hex : ∃ i, b ≤ a + i ∨ x (a + i) ≤ f (a + i) := ⟨b - a, Or.inl (by omega)⟩
  set i0 := Nat.find hex with hi0
  have hspec : b ≤ a + i0 ∨ x (a + i0) ≤ f (a + i0) := Nat.find_spec hex
  have hmin : ∀ i < i0, ¬ (b ≤ a + i ∨ x (a + i) ≤ f (a + i)) := fun i hi => Nat.find_min hex hi
  have hi0b : a + i0 ≤ b := by
    by_contra hc
    have := hmin (b - a) (by omega)
    exact this (Or.inl (by omega))
  set m := a + i0
  refine ⟨m, by omega, hi0b, ?_, ?_⟩
  · apply chain_up f a m
    intro k hak hkm
    have hnot := hmin (k - a) (by omega)
    rw [show a + (k - a) = k by omega] at hnot
    push_neg at hnot
    obtain ⟨θ, h0, h1, hf⟩ := hstep k hak hnot.1
    rw [hf]
    nlinarith
  · -- invariant x k ≤ f k on [m, b)
    have hinv : ∀ k, m ≤ k → k < b → x k ≤ f k := by
      intro k hmk hkb
      induction k with
      | zero =>
        have : m = 0 := by omega
        rcases hspec with h | h
        · omega
        · rw [← this]; exact h
      | succ k ih =>
        rcases Nat.eq_or_lt_of_le hmk with h | h
        · rcases hspec with h' | h'
          · omega
          · rw [← h]; exact h'
        · have hk := ih (by omega) (by omega)
          obtain ⟨θ, h0, h1, hf⟩ := hstep k (by omega) (by omega)
          have hxx := hx k (by omega) hkb
          rw [hf]
          nlinarith
    apply chain_down f m b
    intro k hmk hkb
    have hk := hinv k hmk hkb
    obtain ⟨θ, h0, h1, hf⟩ := hstep k (by omega) hkb
    rw [hf]
    nlinarith

theorem pre_succ {n : ℕ} (A : Fin n ≃ Fin n) (k : ℕ) (hk : k < n) :
    pre A (k + 1) = insert (A ⟨k, hk⟩) (pre A k) ∧ A ⟨k, hk⟩ ∉ pre A k := by
  constructor
  · unfold pre
    rw [← Finset.image_insert]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · subst h; simp
      · omega
  · unfold pre
    simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
    intro p hp hAp
    have := A.injective hAp
    subst this
    simp at hp

theorem etil_le {n : ℕ} (s : DPSeq n) (kmid j : ℕ) : etil s kmid j ≤ n := by
  unfold etil
  simpa using Finset.card_le_univ (U s kmid j)

end RRBC55

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j + 1 ≤ s.T) :
    IsUnimodalOn (revAt I A) (etil s kmid j) (etil s kmid (j + 1)) := by
  have hr := hst.2.1
  have hw := hst.2.2.1
  have hbn := RRBC55.etil_le s kmid (j + 1)
  have hab : etil s kmid j ≤ etil s kmid (j + 1) := by
    unfold etil
    apply Finset.card_le_card
    show U s kmid j ⊆ U s kmid j ∪ deltaStep s kmid (j + 1) (U s kmid j)
    exact Finset.subset_union_left
  let x : ℕ → ℝ := fun k => if h : k < n then I.r (A ⟨k, h⟩) else 0
  apply RRBC55.abstract_unimodal (revAt I A) x _ _ hab
  · intro k _ hkb
    have hkn : k < n := by omega
    obtain ⟨hins, hnot⟩ := RRBC55.pre_succ A k hkn
    have hrev := revenue_insert I hr hw (pre A k) (A ⟨k, hkn⟩) hnot
    have hW : 0 ≤ wt I (pre A k) := Finset.sum_nonneg (fun i _ => (hw i).le)
    have hwi := hw (A ⟨k, hkn⟩)
    refine ⟨(1 + wt I (pre A k)) / (1 + wt I (pre A k) + I.w (A ⟨k, hkn⟩)), ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith
    · unfold revAt
      rw [hins, hrev]
      simp only [x, dif_pos hkn]
      congr 1
      have hD : (1 + wt I (pre A k) + I.w (A ⟨k, hkn⟩)) ≠ 0 := by linarith
      field_simp
      ring
  · intro k hak hkb
    have hkn : k + 1 < n := by omega
    simp only [x, dif_pos hkn, dif_pos (show k < n by omega)]
    have := (hR (j + 1) (by omega) hjT).2 ⟨k, by omega⟩ ⟨k + 1, hkn⟩
    simp only [Nat.add_sub_cancel] at this
    exact this hak (by simp) hkb
