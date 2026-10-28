-- Prove2me | solution 1 for D1Bound5.bennettTwoResidualRate_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:18.852422+00:00
-- url     : https://prove2.me/submissions/4281b228-ca91-4c8b-89af-4ad321d5eade

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Theorems.Thm_D1Bound5_bennettTwoResidualRate_lower

section
namespace D1Bound5





/-- Instantiation with the actual anchor norms and their actual complex
separation. The separation estimate is derived by the triangle inequality. -/
theorem _root_.solution (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖) :
    2 * ‖a‖ * ‖c‖ ^ 2 / (5 * ‖b‖) <
      bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖ :=
  bennettTwoResidualRate_lower ‖a‖ ‖b‖ ‖c‖ ‖a - b‖
    (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) hAB (norm_sub_le a b) hAC

end D1Bound5
end
