-- Prove2me | solution 2 for DiazModulus.log_two_pi_dependent_forces_transcendence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:28.180063+00:00
-- url     : https://prove2.me/submissions/9e671dc6-2ece-4287-a57a-3256642a1441

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_log_pair_square_ratio_transcendental

open Complex ComplexConjugate

namespace S7W1_log_two_pi_dependent_forces_transcendence

theorem isAlg_rat (r : ℚ) : IsAlgebraic ℚ (r : ℂ) :=
  isAlgebraic_algebraMap r

theorem pI_ne_zero : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero

theorem exp_pI_alg : IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_pi_mul_I]; simpa using isAlg_rat (-1)

end S7W1_log_two_pi_dependent_forces_transcendence

open S7W1_log_two_pi_dependent_forces_transcendence in
theorem solution (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) ((Real.log 2 : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp (Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2 / ((Real.log 2 : ℝ) : ℂ))) := by
  have hL0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h₁ : IsAlgebraic ℚ (Complex.exp ((Real.log 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    simpa using isAlg_rat 2
  have hind : ∀ q : ℚ, ((Real.log 2 : ℝ) : ℂ) ≠ (q : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    intro q h
    have h' := congrArg Complex.re h
    rw [Complex.ofReal_re] at h'
    have h0 : ((q : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
    exact hL0 (h'.trans h0)
  obtain ⟨hA, hB⟩ := DiazModulus.log_pair_square_ratio_transcendental _ _ h₁ exp_pI_alg
    pI_ne_zero hind hdep
  constructor
  · intro h
    apply hA
    have e : ((Real.log 2 : ℝ) : ℂ) ^ 2 / (((Real.pi : ℝ) : ℂ) * Complex.I) =
        -(Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ)) := by
      rw [div_mul_eq_div_div, div_eq_mul_inv (((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ)),
        Complex.inv_I]
      ring
    rw [e, Complex.exp_neg]
    exact h.inv
  · intro h
    apply hB
    have e : (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 / ((Real.log 2 : ℝ) : ℂ) =
        -(((Real.pi : ℝ) : ℂ) ^ 2 / ((Real.log 2 : ℝ) : ℂ)) := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [e, Complex.exp_neg]
    exact h.inv

#print axioms solution
