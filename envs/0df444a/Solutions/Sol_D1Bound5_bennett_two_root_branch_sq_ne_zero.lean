-- Prove2me | solution 1 for D1Bound5.bennett_two_root_branch_sq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:54.048722+00:00
-- url     : https://prove2.me/submissions/4478a600-4f8b-400e-ab79-d1101aafea02

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

/-- The principal branch used by the two-anchor approximation has the
required square and is nonzero throughout the actual size range. -/
theorem _root_.solution
    (a c : ℂ) (hsize : 1 < ‖a‖*‖c‖) :
    ((1+1/(a*c))^(1/2 : ℂ))^(2 : ℕ) = 1+1/(a*c) ∧
      (1+1/(a*c))^(1/2 : ℂ) ≠ 0 := by
  have hsquare := coherent_cpow_half_sq (1+1/(a*c))
  refine ⟨hsquare, ?_⟩
  have hprod : 0 < ‖a‖*‖c‖ := by linarith
  have hsmall : ‖1/(a*c)‖ < 1 := by
    rw [norm_div, norm_one, norm_mul]
    exact (div_lt_one hprod).2 hsize
  have hbase : (1 : ℂ)+1/(a*c) ≠ 0 := by
    intro hzero
    have heq : 1/(a*c) = -(1 : ℂ) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hzero)
    have hn : ‖1/(a*c)‖ = 1 := by rw [heq]; norm_num
    linarith
  intro hzero
  rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsquare
  exact hbase hsquare.symm



end D1Bound5
end
