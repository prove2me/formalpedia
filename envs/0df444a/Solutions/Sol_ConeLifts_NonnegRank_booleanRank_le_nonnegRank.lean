-- Prove2me | solution 1 for ConeLifts.NonnegRank.booleanRank_le_nonnegRank
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:18:30.663234+00:00
-- url     : https://prove2.me/submissions/8f3d7f3e-e22c-4dd9-ac99-b24a89c12093

import Mathlib.Tactic

theorem solution {ι κ : Type*} (M : ι → κ → ℝ) (hM : ∀ i j,0 ≤ M i j) (k : ℕ)
    (A : ι → Fin k → ℝ) (B : Fin k → κ → ℝ) (hA : ∀ i l,0 ≤ A i l) (hB : ∀ l j,0 ≤ B l j)
    (hAB : ∀ i j,M i j=∑ l,A i l*B l j) :
    ∃ (A' : ι → Fin k → Bool) (B' : Fin k → κ → Bool),
      ∀ i j,(M i j ≠ 0 ↔ ∃ l,A' i l=true ∧ B' l j=true) := by
  classical
  refine ⟨fun i l => decide (A i l ≠ 0),fun l j => decide (B l j ≠ 0),?_⟩
  intro i j
  simp only [decide_eq_true_eq,hAB i j]
  constructor
  · intro h
    by_contra hn
    apply h
    apply Finset.sum_eq_zero
    intro l hl
    by_cases ha : A i l=0
    · simp [ha]
    · have hb : B l j=0 := by by_contra hb;exact hn ⟨l,ha,hb⟩
      simp [hb]
  · rintro ⟨l,ha,hb⟩
    have hp : 0 < A i l*B l j := mul_pos (lt_of_le_of_ne (hA i l) ha.symm) (lt_of_le_of_ne (hB l j) hb.symm)
    have hh : A i l*B l j ≤ ∑ t,A i t*B t j :=
      Finset.single_le_sum (fun t ht => mul_nonneg (hA i t) (hB t j)) (Finset.mem_univ l)
    exact (hp.trans_le hh).ne'
