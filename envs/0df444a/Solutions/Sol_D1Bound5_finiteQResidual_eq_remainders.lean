-- Prove2me | solution 1 for D1Bound5.finiteQResidual_eq_remainders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:44.585077+00:00
-- url     : https://prove2.me/submissions/6b4d5365-9a8b-49f4-8348-bb1fcc49b9bd

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_finiteQ_half_coefficients

section
open Finset

namespace D1Bound5









set_option maxHeartbeats 800000 in
/-- Every nonnegative power and each inverse power through c^-3 cancels.
The remaining four terms are genuine analytic remainders, not an assumed
formal residual estimate. -/
theorem _root_.solution
    (u v c : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0) :
    finiteQResidual u v c =
      u*(u^2-5*u*v)*finiteQHalfRemainder 4 (1/(u*c)) +
      u*(4*u^3-8*u^2*v)*c*finiteQHalfRemainder 5 (1/(u*c)) +
      v*(5*u*v-v^2)*finiteQHalfRemainder 4 (1/(v*c)) +
      v*(8*u*v^2-4*v^3)*c*finiteQHalfRemainder 5 (1/(v*c)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := finiteQ_half_coefficients
  simp only [finiteQResidual, finiteQHalfRemainder, Finset.sum_range_succ,
    Finset.sum_range_zero, h0, h1, h2, h3, h4]
  norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat, pow_zero, pow_one, zero_add, one_mul]
  unfold finiteQConstant finiteQLeft finiteQRight
  field_simp [hu, hv, hc]
  <;> ring

end D1Bound5
end
