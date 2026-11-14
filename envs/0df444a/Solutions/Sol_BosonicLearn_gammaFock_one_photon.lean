-- Prove2me | solution 1 for BosonicLearn.gammaFock_one_photon
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:12:23.036725+00:00
-- url     : https://prove2.me/submissions/c44c2c82-a6db-4f9c-9c62-9ca67568eb53

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open BosonicLearn

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    gammaFock R (0 : Occupation (Fin n)) 0 = 1 ∧
    gammaFock R (Pi.single i 1 : Occupation (Fin n)) (Pi.single j 1) = R i j := by
  constructor
  · unfold gammaFock
    rw [Finset.sum_eq_single (0 : Fin n → Fin n → ℕ)]
    · simp
    · intro M hM hne
      exfalso
      apply hne
      rw [Finset.mem_filter] at hM
      funext a b
      have h := hM.2.1 a
      simp only [Pi.zero_apply, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at h
      exact h b
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun a b => by simp, fun a => by simp, fun b => by simp⟩
  · have hfact : ∀ k : Fin n, ∀ a : Fin n,
        (Nat.factorial ((Pi.single k 1 : Fin n → ℕ) a) : ℝ) = 1 := by
      intro k a
      by_cases h : a = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    unfold gammaFock
    rw [Finset.sum_eq_single (fun a b => if a = i ∧ b = j then 1 else 0 : Fin n → Fin n → ℕ)]
    · simp only [hfact, Finset.prod_const_one, mul_one, Real.sqrt_one, Complex.ofReal_one, one_mul]
      rw [Finset.prod_eq_single i, Finset.prod_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
      · intro a _ ha
        simp [ha]
      · simp
    · intro M hM hne
      exfalso
      apply hne
      rw [Finset.mem_filter] at hM
      obtain ⟨-, hrow, hcol⟩ := hM
      have hz : ∀ a b, ¬ (a = i ∧ b = j) → M a b = 0 := by
        intro a b hab
        by_cases ha : a = i
        · have hb : b ≠ j := fun hb => hab ⟨ha, hb⟩
          have h := hcol b
          rw [Pi.single_eq_of_ne hb] at h
          simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at h
          exact h a
        · have h := hrow a
          rw [Pi.single_eq_of_ne ha] at h
          simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at h
          exact h b
      funext a b
      by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        have h := hrow a
        rw [Finset.sum_eq_single b (fun c _ hc => hz a c (fun h => hc h.2)) (by simp)] at h
        simpa using h
      · rw [hz a b hab, if_neg hab]
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
      · by_cases ha : a = i
        · subst ha; split_ifs <;> simp
        · simp [ha]
      · by_cases ha : a = i
        · subst ha; simp
        · simp [ha]
      · by_cases hb : b = j
        · subst hb; simp
        · simp [hb]
