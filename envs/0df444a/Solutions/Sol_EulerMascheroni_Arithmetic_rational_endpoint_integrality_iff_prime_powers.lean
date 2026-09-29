-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_prime_powers
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:03:33.055976+00:00
-- url     : https://prove2.me/submissions/e28c8a16-dbb7-443f-b3ce-8bcee817c295

import Theorems.Thm_EulerMascheroni_Arithmetic_rational_endpoint_integrality_iff_divisibility
namespace EulerPrimeDivisibility
lemma int_dvd_iff_prime_powers (a b : ℤ) :
    a ∣ b ↔ ∀ p k : ℕ, p.Prime → (p^k:ℤ) ∣ a → (p^k:ℤ) ∣ b := by
  constructor
  · intro h p k hp hpa; exact hpa.trans h
  · intro h
    apply Int.natAbs_dvd_natAbs.mp
    apply (Nat.dvd_iff_prime_pow_dvd_dvd b.natAbs a.natAbs).mpr
    intro p k hp hpa
    have h' := h p k hp (by exact_mod_cast (Int.natCast_dvd.mpr hpa))
    exact Int.natCast_dvd.mp (by exact_mod_cast h')
end EulerPrimeDivisibility
open EulerMascheroni.Arithmetic
namespace EulerEndpointPrimes
lemma integral_iff_prime_powers (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      ∀ p k : ℕ, p.Prime → (p^k:ℤ) ∣ B*(m.factorial:ℤ) →
        (p^k:ℤ) ∣ (D:ℤ)*(A-B*∑ j ∈ Finset.range m, (-1:ℤ)^j*j.factorial) := by
  rw [rational_endpoint_integrality_iff_divisibility A B hB D m]
  exact EulerPrimeDivisibility.int_dvd_iff_prime_powers _ _
end EulerEndpointPrimes

theorem solution (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      ∀ p k : ℕ, p.Prime → (p^k:ℤ) ∣ B*(m.factorial:ℤ) →
        (p^k:ℤ) ∣ (D:ℤ)*(A-B*∑ j ∈ Finset.range m, (-1:ℤ)^j*j.factorial) := by
  exact EulerEndpointPrimes.integral_iff_prime_powers A B hB D m

#print axioms solution
