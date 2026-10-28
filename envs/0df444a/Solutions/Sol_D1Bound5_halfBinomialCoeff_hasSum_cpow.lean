-- Prove2me | solution 1 for D1Bound5.halfBinomialCoeff_hasSum_cpow
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:30.688457+00:00
-- url     : https://prove2.me/submissions/6939d66c-7cea-4c85-97ba-734d47e0f4f8

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
namespace D1Bound5

/-- The half-binomial coefficients sum to the complex principal power
of exponent one half throughout the open unit disk. -/
theorem _root_.solution (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (halfBinomialCoeff n : ℂ) * z ^ n)
      ((1 + z) ^ (1 / 2 : ℂ)) := by
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hs := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (1 / 2 : ℂ))).hasSum_sub hzball
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    halfBinomialCoeff, Complex.ofReal_choose, smul_eq_mul, mul_comm] using hs







end D1Bound5
end
