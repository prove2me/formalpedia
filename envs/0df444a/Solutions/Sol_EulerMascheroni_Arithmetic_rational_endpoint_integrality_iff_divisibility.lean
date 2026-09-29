-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:42.396998+00:00
-- url     : https://prove2.me/submissions/497f1976-4ee1-4921-8950-036fa4c6ff0c

import Definitions.Def_eulerMascheroni_factorialQuotient
open scoped BigOperators
open EulerMascheroni.Arithmetic
namespace EulerEndpointDivisibility

lemma rational_real_integral_iff (r : ℚ) :
    IsIntegral ℤ (r:ℝ) ↔ ∃ z : ℤ, (r:ℝ) = z := by
  change IsIntegral ℤ (algebraMap ℚ ℝ r) ↔ _
  rw [isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℝ)]
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z, by exact_mod_cast hz.symm⟩
  · rintro ⟨z,hz⟩
    exact ⟨z, by exact_mod_cast hz.symm⟩

lemma rational_scaled_integral_iff (A B : ℤ) (hB : B ≠ 0) (D : ℕ) :
    IsIntegral ℤ ((D:ℝ)*((A:ℝ)/(B:ℝ))) ↔ B ∣ (D:ℤ)*A := by
  have hr := rational_real_integral_iff ((D:ℚ)*((A:ℚ)/(B:ℚ)))
  push_cast at hr
  rw [hr]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    have hh : (D:ℝ)*A = (B:ℝ)*z := by
      push_cast at hz
      field_simp at hz
      nlinarith [hz]
    exact_mod_cast hh
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    push_cast
    have hh : (D:ℝ)*A = (B:ℝ)*z := by exact_mod_cast hz
    have hb : (B:ℝ) ≠ 0 := by exact_mod_cast hB
    field_simp
    nlinarith [hh]

lemma quotient_integral_iff (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      B*(m.factorial:ℤ) ∣ (D:ℤ)*(A-B*∑ k ∈ Finset.range m, (-1:ℤ)^k*k.factorial) := by
  have hf : (m.factorial:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by exact_mod_cast hB
  have he : quotientCoeff ((A:ℝ)/(B:ℝ)) m =
      ((A-B*∑ k ∈ Finset.range m, (-1:ℤ)^k*k.factorial : ℤ):ℝ) /
        ((B*(m.factorial:ℤ):ℤ):ℝ) := by
    unfold quotientCoeff
    push_cast
    field_simp
  rw [he]
  exact rational_scaled_integral_iff _ _ (mul_ne_zero hB (by exact_mod_cast Nat.factorial_ne_zero m)) D
end EulerEndpointDivisibility


theorem solution (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      B*(m.factorial:ℤ) ∣ (D:ℤ)*(A-B*∑ k ∈ Finset.range m, (-1:ℤ)^k*k.factorial) := by
  exact EulerEndpointDivisibility.quotient_integral_iff A B hB D m

#print axioms solution
