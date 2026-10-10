-- Prove2me | solution 1 for BookProof.ChapterE4.wave_prob_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:01:40.107787+00:00
-- url     : https://prove2.me/submissions/55f7db0e-fee9-48d2-a86a-55d4d97c333a

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.wave_prob_sum
import Mathlib
import Definitions.Def_ChapterE4
import Theorems.Thm_BookProof_ChapterE4_wave_eq_zero_of_lt
import Theorems.Thm_BookProof_ChapterE4_diag_collapse
open BookProof.ChapterE4



open scoped BigOperators


@[simp] private theorem wave_zero (θ : ℕ → ℝ) (s : ℕ) : wave θ s 0 = basisVec s := rfl

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (s d : ℕ) :
    ∑ i ∈ Finset.Icc s (s + d), (wave θ s d i) ^ 2 = 1 := by

  induction d generalizing s with
  | zero => ?_
  | succ d ih => ?_
  · simp [ wave_zero, basisVec ];
  · -- Apply the_diag_collapse theorem to rewrite the sum.
    have h_sum : ∑ i ∈ Finset.Icc s (s + d + 1),      (wave θ s (d + 1) i) ^ 2 = (Real.cos (θ s)) ^
        2 * (∑ i ∈ Finset.Icc s (s + d + 1), (basisVec s i) ^ 2) + (Real.sin (θ s)) ^ 2 * (∑ i ∈
            Finset.Icc s (s + d + 1), (wave θ (s + 1) d i) ^ 2) := by
      rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _, ← Finset.sum_add_distrib ] ;        exact
          Finset.sum_congr rfl fun _ _ => diag_collapse θ s d _;
    -- Evaluate the sums using the properties of the basis vectors and the induction hypothesis.
    have h_basis : ∑ i ∈ Finset.Icc s (s + d + 1), (basisVec s i) ^ 2 = 1 := by
      rw [ Finset.sum_eq_single s ] <;> simp +contextual [ basisVec ];
      linarith
    have h_ind : ∑ i ∈ Finset.Icc s (s + d + 1), (wave θ (s + 1) d i) ^ 2 = 1 := by
      convert ih (s + 1) using 1
      rw [show s + 1 + d = s + d + 1 by ring, Finset.Icc_eq_cons_Ioc (by linarith),
        Finset.sum_cons]
      have hIcc : Finset.Icc (s + 1) (s + d + 1) = Finset.Ioc s (s + d + 1) := by
        ext; aesop
      rw [hIcc, show wave θ (s + 1) d s = 0 from wave_eq_zero_of_lt _ _ _ _ (by linarith)]
      norm_num
    simp_all [← add_assoc]
