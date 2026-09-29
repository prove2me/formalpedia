-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.factorial_denominators_iff_prime_local_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:03:32.537502+00:00
-- url     : https://prove2.me/submissions/3ae0ecb3-5458-4676-8974-7748ce756b1a

import Definitions.Def_eulerMascheroni_factorialQuotient
import Theorems.Thm_EulerMascheroni_Arithmetic_quotient_coefficient_properties
import Theorems.Thm_EulerMascheroni_Arithmetic_integral_of_prime_local_multiples
open EulerMascheroni.Arithmetic
namespace EulerLocalDenominators
lemma integral_prefix_iff (a : ℝ) (D n : ℕ) :
    (∀ k : ℕ, k ≤ n → IsIntegral ℤ ((D:ℝ)*quotientCoeff a k)) ↔
      IsIntegral ℤ ((D:ℝ)*quotientCoeff a n) := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h
    induction n with
    | zero =>
      intro k hk
      have he : k=0 := by omega
      simpa [he] using h
    | succ n ih =>
      have hn : IsIntegral ℤ ((D:ℝ)*quotientCoeff a n) := by
        have hrec := ((quotient_coefficient_properties a).2 n).1
        have hi := ((isIntegral_natCast (n+1) : IsIntegral ℤ ((n+1:ℕ):ℝ)).mul h).add
          ((isIntegral_natCast D : IsIntegral ℤ (D:ℝ)).mul
            ((isIntegral_one : IsIntegral ℤ (1:ℝ)).neg.pow n))
        have heq : (D:ℝ)*quotientCoeff a n =
            ((n+1:ℕ):ℝ)*((D:ℝ)*quotientCoeff a (n+1))+(D:ℝ)*(-1:ℝ)^n := by
          linear_combination -(D:ℝ)*hrec
        rw [heq]
        exact hi
      intro k hk
      by_cases he : k=n+1
      · simpa [he] using h
      · exact ih hn k (by omega)

lemma prime_local_iff (a : ℝ) :
    ExponentialDenominators a ↔
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧ (D:ℝ) ≤ C^(n+1) ∧
      ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧
        IsIntegral ℤ ((d:ℝ)*((D:ℝ)*quotientCoeff a n)) := by
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro n
    obtain ⟨D,hD,hbound,hi⟩ := h n
    refine ⟨D,hD,hbound,?_⟩
    intro p hp
    refine ⟨1,?_,?_⟩
    · exact_mod_cast hp.not_dvd_one
    · simpa using hi n le_rfl
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro n
    obtain ⟨D,hD,hbound,hi⟩ := h n
    refine ⟨D,hD,hbound,?_⟩
    exact (integral_prefix_iff a D n).mpr
      (EulerMascheroni.Arithmetic.integral_of_prime_local_multiples ((D:ℝ)*quotientCoeff a n) hi)
end EulerLocalDenominators


theorem solution (a : ℝ) :
    ExponentialDenominators a ↔
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧ (D:ℝ) ≤ C^(n+1) ∧
      ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧
        IsIntegral ℤ ((d:ℝ)*((D:ℝ)*quotientCoeff a n)) := by
  exact EulerLocalDenominators.prime_local_iff a

#print axioms solution
