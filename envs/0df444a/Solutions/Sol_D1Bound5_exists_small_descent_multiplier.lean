-- Prove2me | solution 1 for D1Bound5.exists_small_descent_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:20:17.059932+00:00
-- url     : https://prove2.me/submissions/a026d540-4988-44e3-a2ef-648b84c5aacb

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- A reciprocal pair of complex multipliers with the indicated trace
bound has one multiplier strictly inside the disk of radius one fifth. -/
theorem _root_.solution (p r0 : ℂ)
    (hr0 : r0^2 = p+1) (hhyper : 7 ≤ ‖2*p+1‖^2) :
    ∃ eta : ℂ, eta^2 = p ∧ ‖2*p+1-2*r0*eta‖ < (1/5 : ℝ) := by
  obtain ⟨eta, heta⟩ := IsAlgClosed.exists_pow_nat_eq p (by decide : 0 < 2)
  have hprod : (2*p+1+2*r0*eta)*(2*p+1-2*r0*eta) = 1 := by
    calc
      _ = (2*p+1)^2-4*r0^2*eta^2 := by ring
      _ = 1 := by rw [hr0, heta]; ring
  have hprodN : ‖2*p+1+2*r0*eta‖*‖2*p+1-2*r0*eta‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hsum : 2*‖2*p+1‖ ≤ ‖2*p+1+2*r0*eta‖+‖2*p+1-2*r0*eta‖ := by
    calc
      2*‖2*p+1‖ = ‖(2*p+1+2*r0*eta)+(2*p+1-2*r0*eta)‖ := by
        rw [show (2*p+1+2*r0*eta)+(2*p+1-2*r0*eta) = 2*(2*p+1) by ring,
          norm_mul, Complex.norm_two]
      _ ≤ _ := norm_add_le _ _
  by_cases hsmall : ‖2*p+1-2*r0*eta‖ < (1/5 : ℝ)
  · exact ⟨eta, heta, hsmall⟩
  · have hsmall' : ‖2*p+1+2*r0*eta‖ < (1/5 : ℝ) := by
      by_contra h
      have hp : (1/5 : ℝ) ≤ ‖2*p+1+2*r0*eta‖ := le_of_not_gt h
      have hm : (1/5 : ℝ) ≤ ‖2*p+1-2*r0*eta‖ := le_of_not_gt hsmall
      have hp5 : ‖2*p+1+2*r0*eta‖ ≤ 5 := by
        nlinarith only [hprodN, mul_nonneg (norm_nonneg (2*p+1+2*r0*eta))
          (sub_nonneg.mpr hm)]
      have hm5 : ‖2*p+1-2*r0*eta‖ ≤ 5 := by
        nlinarith only [hprodN, mul_nonneg (norm_nonneg (2*p+1-2*r0*eta))
          (sub_nonneg.mpr hp)]
      have hsum5 : ‖2*p+1+2*r0*eta‖+‖2*p+1-2*r0*eta‖ ≤ (26/5 : ℝ) := by
        nlinarith only [hprodN,
          mul_nonneg (sub_nonneg.mpr hp5) (sub_nonneg.mpr hm5)]
      have hy : ‖2*p+1‖ ≤ (13/5 : ℝ) := by linarith only [hsum, hsum5]
      have hysq : ‖2*p+1‖^2 ≤ (13/5 : ℝ)^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hy)
          (by positivity : 0 ≤ (13/5 : ℝ)+‖2*p+1‖)]
      nlinarith only [hhyper, hysq]
    refine ⟨-eta, by simpa only [neg_sq] using heta, ?_⟩
    convert hsmall' using 1 <;> congr 1 <;> ring



end D1Bound5
end
