-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:59.882787+00:00
-- url     : https://prove2.me/submissions/36221a5f-5c07-4dbf-b75e-7709ff5e1224

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) :
    l1dist (push P p) (push P q) ≤ (1 - m * eps) * l1dist p q := by

  have hzero : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  have hstep : ∀ j : Fin m,
      |push P p j - push P q j| ≤ ∑ i, |p i - q i| * (P i j - eps) := by
    intro j
    have hdiff : push P p j - push P q j = ∑ i, (p i - q i) * (P i j - eps) := by
      have h1 : ∑ i, (p i - q i) * (P i j - eps)
          = (∑ i, (p i - q i) * P i j) - (∑ i, (p i - q i)) * eps := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, hzero, zero_mul, sub_zero]
      simp only [push, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by
      rw [abs_mul, abs_of_nonneg (by linarith [hmin i j] : (0 : ℝ) ≤ P i j - eps)]
  calc l1dist (push P p) (push P q) ≤ ∑ j, ∑ i, |p i - q i| * (P i j - eps) :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = ∑ i, |p i - q i| * (1 - m * eps) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_sub_distrib, hP.2 i]
        simp [Finset.card_univ, mul_comm]
    _ = (1 - m * eps) * l1dist p q := by
        rw [l1dist, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
