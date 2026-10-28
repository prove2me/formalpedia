-- Prove2me | solution 1 for D1Bound5.bennett_negative_binomial_abs_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:41:08.703589+00:00
-- url     : https://prove2.me/submissions/d527e99a-e05d-4791-9d1b-4ced762a37d4

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
An elementary analytic majorant for the actual binomial/homogeneous tail that
arises in Bennett's simultaneous approximants.  In contrast to a coefficient
envelope interface, every coefficient of the series below is specified.

The algebraic identification of the residue moments with homogeneous
polynomials is a separate theorem.  This file does not assume that an arbitrary
series is a Bennett residual.  Once that identification is available, the
specialization n = 3k, s = k + 1/2 gives exactly the eta exponent in the paper.
-/

namespace D1Bound5

theorem bennett_multichoose_pos (q : ℝ) (hq : 0 < q) (t : ℕ) :
    0 < Ring.multichoose q t := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer q t
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  have hp := ascPochhammer_pos t q hq
  have hf : 0 < (t.factorial : ℝ) := by positivity
  nlinarith

/-- The sign of a negative-upper binomial coefficient disappears into a
positive multichoose coefficient. -/
theorem bennett_choose_negative_abs (q : ℝ) (hq : 0 < q) (t : ℕ) :
    |Ring.choose (-q) t| = Ring.choose (q + t - 1) t := by
  rw [Ring.choose_neg', Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_pos (bennett_multichoose_pos q hq t), Ring.multichoose_eq]



/-- Exact real sum of the absolute negative-binomial series, using the analytic
binomial theorem already proved in mathlib. -/
theorem _root_.solution (q r : ℝ)
    (hq : 0 < q) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun t : ℕ => |Ring.choose (-q) t| * r ^ t)
      (1 / (1 - r) ^ q) := by
  have hrball : r ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hr1
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero q).hasSum_sub hrball
  simpa only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, mul_comm, bennett_choose_negative_abs q hq] using hs





end D1Bound5
end
