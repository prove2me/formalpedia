-- Prove2me | solution 1 for FoundationsRL.PosteriorSampling.decoupling_posterior_means
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:14:51.371922+00:00
-- url     : https://prove2.me/submissions/a7a9a428-f6a3-4e46-81a9-af4353671231

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_posterior

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace Aux_PSdecoup

theorem key {A : ℕ} (p : Fin A → ℝ) (hp : ∀ a, 0 ≤ p a) (Δ : Fin A → Fin A → ℝ) :
    ∑ a, p a * Δ a a ≤ Real.sqrt ((A : ℝ) * ∑ a, ∑ a', p a * p a' * Δ a' a ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin A => (1 : ℝ))
    (fun a => p a * Δ a a)
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at hcs
  have hdiag : ∑ a, (p a * Δ a a) ^ 2 ≤ ∑ a, ∑ a', p a * p a' * Δ a' a ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    have := Finset.single_le_sum (f := fun a' => p a * p a' * Δ a' a ^ 2)
      (fun a' _ => mul_nonneg (mul_nonneg (hp a) (hp a')) (sq_nonneg _)) (Finset.mem_univ a)
    calc (p a * Δ a a) ^ 2 = p a * p a * Δ a a ^ 2 := by ring
      _ ≤ _ := this
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have h2 : (∑ a, p a * Δ a a) ^ 2 ≤ (A : ℝ) * ∑ a, ∑ a', p a * p a' * Δ a' a ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hdiag hA)
  exact (le_abs_self _).trans (Real.abs_le_sqrt h2)

end Aux_PSdecoup

open FoundationsRL.PosteriorSampling in
theorem solution {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (π : BanditPolicy A) (t : ℕ) (h : BanditHistory A t) :
    ∑ a, (π.select t h {a}).toReal *
        (postMeanGiven μ sel π t h a a - postMean μ sel π t h a) ≤
      Real.sqrt ((A : ℝ) * ∑ a, ∑ a', (π.select t h {a}).toReal * (π.select t h {a'}).toReal *
        (postMeanGiven μ sel π t h a' a - postMean μ sel π t h a) ^ 2) :=
  Aux_PSdecoup.key (fun a => (π.select t h {a}).toReal) (fun _ => ENNReal.toReal_nonneg)
    (fun a' a => postMeanGiven μ sel π t h a' a - postMean μ sel π t h a)
