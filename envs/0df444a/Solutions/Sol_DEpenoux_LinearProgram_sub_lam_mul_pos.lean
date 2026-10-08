-- Prove2me | solution 1 for DEpenoux.LinearProgram.sub_lam_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:25:01.511424+00:00
-- url     : https://prove2.me/submissions/2fe958e5-840f-4d22-90fa-8e15e5626b71

import Mathlib

set_option autoImplicit false

theorem dep20e1_exists_pos {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  have : ∑ i ∈ s, f i ≤ 0 := Finset.sum_nonpos hc
  linarith

open Matrix in
theorem solution {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (hirr : ∀ i k, ∃ n : ℕ, 0 < (P ^ n) i k)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (u : Fin m → ℝ)
    (h : ∀ i, 0 ≤ u i - lam * Matrix.mulVec P u i)
    (hne : ∃ i, u i - lam * Matrix.mulVec P u i ≠ 0) :
    ∀ i, 0 < u i := by
  obtain ⟨k, hk⟩ := hne
  have hwk : 0 < u k - lam * Matrix.mulVec P u k := lt_of_le_of_ne (h k) (Ne.symm hk)
  -- Step 1: u ≥ 0
  have hu0 : ∀ i, 0 ≤ u i := by
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ u ⟨k, Finset.mem_univ _⟩
    have hPu : u i0 ≤ Matrix.mulVec P u i0 := by
      simp only [Matrix.mulVec, dotProduct]
      calc u i0 = ∑ j, P i0 j * u i0 := by rw [← Finset.sum_mul, hP1, one_mul]
        _ ≤ ∑ j, P i0 j * u j := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ _)) (hP0 i0 j)
    have h1 := h i0
    have hmin : 0 ≤ u i0 := by nlinarith
    intro i
    exact le_trans hmin (hi0 i (Finset.mem_univ _))
  -- Step 2: zero set is closed
  have hclosed : ∀ i j, u i = 0 → 0 < P i j → u j = 0 ∧ u i - lam * Matrix.mulVec P u i = 0 := by
    intro i j hi hpij
    have hterm : ∀ l, 0 ≤ P i l * u l := fun l => mul_nonneg (hP0 i l) (hu0 l)
    have hsum : 0 ≤ Matrix.mulVec P u i := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_nonneg (fun l _ => hterm l)
    have hwi := h i
    have hz : Matrix.mulVec P u i = 0 := by
      rw [hi] at hwi
      have : lam * Matrix.mulVec P u i ≤ 0 := by linarith
      have h2 : Matrix.mulVec P u i ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have := mul_pos hlam0 hc
        linarith
      linarith
    refine ⟨?_, by rw [hi, hz]; ring⟩
    have hz' : ∑ l, P i l * u l = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hterm l)).1 hz' j (Finset.mem_univ _)
    rcases mul_eq_zero.1 hall with h3 | h3
    · exact absurd h3 (ne_of_gt hpij)
    · exact h3
  have hpow : ∀ n : ℕ, ∀ i j, u i = 0 → 0 < (P ^ n) i j → u j = 0 := by
    intro n
    induction n with
    | zero =>
      intro i j hi hp
      rw [pow_zero] at hp
      by_cases hij : i = j
      · subst hij; exact hi
      · simp [hij] at hp
    | succ n ih =>
      intro i j hi hp
      rw [pow_succ, Matrix.mul_apply] at hp
      obtain ⟨l, -, hl⟩ := dep20e1_exists_pos _ _ hp
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hl with ⟨ha, hb⟩ | ⟨-, hb⟩
      · exact (hclosed l j (ih i l hi ha) hb).1
      · exact absurd (hP0 l j) (not_le.2 hb)
  intro i
  rcases (hu0 i).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨n, hn⟩ := hirr i k
    have hk0 := hpow n i k heq.symm hn
    have hs : (0:ℝ) < ∑ j, P k j := by rw [hP1]; exact one_pos
    obtain ⟨j, -, hj⟩ := dep20e1_exists_pos _ _ hs
    have := (hclosed k j hk0 hj).2
    exact hk this
