-- Prove2me | solution 1 for D1Bound5.bennett_two_root_branch_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:00:27.375329+00:00
-- url     : https://prove2.me/submissions/233e3ea4-852d-4f16-879a-ecfb4d50466c

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq

section
namespace D1Bound5



/-- A uniform bound on the same actual branch. The weak rational constant
is chosen to leave room in the later signed-root approximation. -/
theorem _root_.solution
    (a c : ℂ) (hsize : 1000 ≤ ‖a‖*‖c‖) :
    ‖(1+1/(a*c))^(1/2 : ℂ)‖ < (6/5 : ℝ) := by
  have hprod : 0 < ‖a‖*‖c‖ := by linarith
  have hinv : ‖1/(a*c)‖ ≤ (1/1000 : ℝ) := by
    rw [norm_div, norm_one, norm_mul]
    apply (div_le_div_iff₀ hprod (by norm_num : (0 : ℝ) < 1000)).2
    simpa using hsize
  have hnorm : ‖(1+1/(a*c))^(1/2 : ℂ)‖^2 = ‖1+1/(a*c)‖ := by
    rw [← norm_pow, coherent_cpow_half_sq]
  have hbound := norm_add_le (1 : ℂ) (1/(a*c))
  rw [norm_one] at hbound
  have hnonneg := norm_nonneg ((1+1/(a*c))^(1/2 : ℂ))
  nlinarith only [hinv, hnorm, hbound, hnonneg]

end D1Bound5
end
