-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.factorial_partial_sum_congruence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:37:53.090668+00:00
-- url     : https://prove2.me/submissions/78c1aee7-077f-4e2a-b707-055747a37e3e

import Definitions.Def_eulerMascheroni_factorialQuotient
set_option autoImplicit false
open EulerMascheroni.Arithmetic

namespace EulerArithmeticWork

def factorialPartialSum (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1 : ℤ)^k * (k.factorial : ℤ)

lemma partial_sum_congruence (n m : ℕ) (h : n ≤ m) :
    (n.factorial : ℤ) ∣ factorialPartialSum m - factorialPartialSum n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hf : (n.factorial : ℤ) ∣ (m.factorial : ℤ) := by
      exact_mod_cast Nat.factorial_dvd_factorial hm
    have ht : (n.factorial : ℤ) ∣ (-1 : ℤ)^m * (m.factorial : ℤ) :=
      dvd_mul_of_dvd_right hf _
    have heq : factorialPartialSum (m+1) - factorialPartialSum n =
        (factorialPartialSum m - factorialPartialSum n) + (-1 : ℤ)^m * (m.factorial : ℤ) := by
      simp only [factorialPartialSum, Finset.sum_range_succ]
      ring
    rw [heq]
    exact dvd_add ih ht

lemma denominator_congruence (a D : ℤ) (n : ℕ) :
    (∃ m : ℤ, (D : ℝ) * quotientCoeff (a : ℝ) n = (m : ℝ)) ↔
      (n.factorial : ℤ) ∣ D * (a - factorialPartialSum n) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hs : (factorialPartialSum n : ℝ) =
      ∑ k ∈ Finset.range n, (-1 : ℝ)^k * (k.factorial : ℝ) := by
    simp [factorialPartialSum]
  simp only [quotientCoeff, ← hs]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Int.cast_injective (α := ℝ)
    push_cast
    field_simp at hm
    linear_combination hm
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hm' : (D : ℝ) * ((a : ℝ) - (factorialPartialSum n : ℝ)) =
        (n.factorial : ℝ) * (m : ℝ) := by exact_mod_cast hm
    field_simp
    linear_combination hm'

end EulerArithmeticWork


theorem solution (n m : ℕ) (h : n ≤ m) :
    (n.factorial : ℤ) ∣
      (∑ k ∈ Finset.range m, (-1 : ℤ)^k * (k.factorial : ℤ)) -
      (∑ k ∈ Finset.range n, (-1 : ℤ)^k * (k.factorial : ℤ)) := by
  exact EulerArithmeticWork.partial_sum_congruence n m h

#print axioms solution
