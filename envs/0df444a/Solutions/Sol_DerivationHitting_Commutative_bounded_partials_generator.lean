-- Prove2me | solution 1 for DerivationHitting.Commutative.bounded_partials_generator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:53:26.357772+00:00
-- url     : https://prove2.me/submissions/429d5583-db0e-4956-b91c-285abee69ab6

import Mathlib
import Theorems.Thm_DerivationHitting_Commutative_logarithm_order_bound

section
open DerivationHitting.Commutative

namespace DerivationHitting.Dev.Gen
noncomputable section

variable {F : Type*} [Field F]

lemma agree_mul (c : ℕ) {a a' b b' : PowerSeries F}
    (ha : ∀ k ≤ c, PowerSeries.coeff k a = PowerSeries.coeff k a')
    (hb : ∀ k ≤ c, PowerSeries.coeff k b = PowerSeries.coeff k b') :
    ∀ k ≤ c, PowerSeries.coeff k (a * b) = PowerSeries.coeff k (a' * b') := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [ha p.1 (by omega), hb p.2 (by omega)]

lemma coeff_gen {n : ℕ} (r : ℕ) (i : Fin n) (k : ℕ) (hk : k ≤ cutoff n r) :
    PowerSeries.coeff k ((generator (F := F) n r i : Polynomial F) : PowerSeries F)
      = PowerSeries.coeff k (formalLogarithm i) := by
  rw [Polynomial.coeff_coe, generator, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, formalLogarithm, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma agree {n : ℕ} (r : ℕ) (f : MvPolynomial (Fin n) F) :
    ∀ k ≤ cutoff n r, PowerSeries.coeff k (logarithmSubstitution n f)
      = PowerSeries.coeff k ((polynomialSubstitution n r f : Polynomial F) : PowerSeries F) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro k hk
    simp [logarithmSubstitution, polynomialSubstitution]
  | add p q hp hq =>
    intro k hk
    simp only [map_add]
    simp [hp k hk, hq k hk]
  | mul_X p i hp =>
    have := agree_mul (cutoff n r) hp (fun k hk => (coeff_gen r i k hk).symm)
    intro k hk
    have h := this k hk
    simpa [logarithmSubstitution, polynomialSubstitution] using h

end
end DerivationHitting.Dev.Gen

namespace DerivationHitting.Commutative

theorem chk_bounded_partials_generator {F : Type*} [Field F] [CharZero F] (n r : ℕ) :
    (∀ i : Fin n, (generator (F := F) n r i).natDegree ≤ cutoff n r ∧
      (generator (F := F) n r i).natDegree ≤ 2 * n * r ^ 2) ∧
    (∀ f : MvPolynomial (Fin n) F, hasBoundedPartials f r →
      (f = 0 ↔ polynomialSubstitution n r f = 0)) := by
  refine ⟨fun i => ?_, fun f hf => ?_⟩
  · have h1 : (generator (F := F) n r i).natDegree ≤ cutoff n r := by
      rw [generator]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
      intro k hk
      exact (Polynomial.natDegree_monomial_le _).trans (by have := Finset.mem_range.1 hk; omega)
    refine ⟨h1, h1.trans ?_⟩
    have hn : 1 ≤ n := by have := i.2; omega
    unfold cutoff
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · have : r ≤ n * r ^ 2 := by nlinarith
      nlinarith
  · constructor
    · rintro rfl; exact map_zero _
    · intro h
      by_contra hne
      obtain ⟨k, hk, hk0⟩ := DerivationHitting.Commutative.logarithm_order_bound r f hne hf
      apply hk0
      rw [DerivationHitting.Dev.Gen.agree r f k hk.le, h]
      simp

end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_bounded_partials_generator := @DerivationHitting.Commutative.chk_bounded_partials_generator
