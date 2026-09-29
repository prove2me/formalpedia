-- Prove2me | solution 2 for DiazModulus.exp_abs_log_two_add_i_pi_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:18:58.497799+00:00
-- url     : https://prove2.me/submissions/e06eb11d-da41-4189-95a7-df0e01c3a6e6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_exp_abs_transcendental_of_isAlgebraic_adjoin

open Complex ComplexConjugate

namespace S7W1_exp_abs_log_two_add_i_pi

/-- Every `x` is algebraic over `ℚ[x]`: it is the image of the generator of `ℚ[x]`. -/
theorem self_isAlgebraic (x : ℂ) : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) x :=
  isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin ℚ ({x} : Set ℂ)))

end S7W1_exp_abs_log_two_add_i_pi

open S7W1_exp_abs_log_two_add_i_pi in
theorem solution (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) ((Real.log 2 : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp ((Real.sqrt (Real.log 2 ^ 2 + Real.pi ^ 2) : ℝ) : ℂ)) := by
  -- The node with `λ := log 2 + iπ` and `x := iπ`.
  have hnorm : ‖((Real.log 2 : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I‖ =
      Real.sqrt (Real.log 2 ^ 2 + Real.pi ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  -- `exp (log 2 + iπ) = 2 · (-1) = -2`.
  have hexp : IsAlgebraic ℚ
      (Complex.exp (((Real.log 2 : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by norm_num), Complex.exp_pi_mul_I]
    simpa using (isAlgebraic_algebraMap (-2 : ℚ) : IsAlgebraic ℚ ((-2 : ℚ) : ℂ))
  have him : (((Real.log 2 : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I).im ≠ 0 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    exact Real.pi_ne_zero
  have hcl : conj (((Real.log 2 : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I) =
      ((Real.log 2 : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  -- `log 2 ± iπ` are algebraic over `ℚ[iπ]`, since `log 2` is by hypothesis and `iπ ∈ ℚ[iπ]`.
  have hpi := self_isAlgebraic (((Real.pi : ℝ) : ℂ) * Complex.I)
  have h := DiazModulus.exp_abs_transcendental_of_isAlgebraic_adjoin _ _ hexp him
    (hdep.add hpi) (by rw [hcl]; exact hdep.sub hpi)
  rwa [hnorm] at h

#print axioms solution
