-- Prove2me | solution 1 for DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:41:54.188223+00:00
-- url     : https://prove2.me/submissions/1b2650ea-c57f-4b29-86a8-86bd30bb9eaf

import Mathlib
import Theorems.Thm_DiazModulus_two_algebraically_independent_of_exp_column
import Theorems.Thm_DiazModulus_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi

/-!
# Two of `π`, `e`, `e^{π²}` are algebraically independent when `e^{ir/π}` is algebraic

`DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi` proves this under the hypothesis `hW73`,
Waldschmidt's theorem of 1973. `DiazModulus.two_algebraically_independent_of_exp_column` is that
theorem, stated as exactly the proposition `hW73`, so it discharges the hypothesis.
-/

theorem solution
    (r : ℚ) (hr : r ≠ 0)
    (halg : IsAlgebraic ℚ (Complex.exp (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)))) :
    ∃ a ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
      ∃ b ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
        AlgebraicIndependent ℚ ![a, b] := by
  exact DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi
    DiazModulus.two_algebraically_independent_of_exp_column r hr halg
