-- Prove2me | solution 1 for FunctionalInequalities.Analysis.jordan_trace_domination_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:46:04.063446+00:00
-- url     : https://prove2.me/submissions/2ba4ef6f-2080-4124-a5a2-5d3310669bfd

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section JordanTrace
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- A mixed weighted trace is nonnegative. The weight need only be symmetric;
it need not be positive semidefinite. -/
theorem FunctionalInequalities.Analysis.trace_cross_nonneg {P N H : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
    0 ≤ (P * H * N * H).trace := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  have he : (P * H * N * H).trace =
      ((X * H) * N * (X * H).conjTranspose).trace := by
    simp only [hX, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hH.eq]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm X.transpose (X * H * N * H))
  rw [he]
  exact (hN.mul_mul_conjTranspose_same (X * H)).trace_nonneg
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Jordan decomposition gives pointwise trace-energy domination for every
symmetric weight, without a commutation assumption. -/
theorem solution {P N H : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
    ((P - N) * H * (P - N) * H).trace ≤
      (P * H * P * H).trace + (N * H * N * H).trace := by
  have hPNH := FunctionalInequalities.Analysis.trace_cross_nonneg (P := P) (N := N) hP hN hH
  have hNPH := FunctionalInequalities.Analysis.trace_cross_nonneg (P := N) (N := P) hN hP hH
  have hexpand :
      ((P - N) * H * (P - N) * H).trace =
        (P * H * P * H).trace - (P * H * N * H).trace -
          (N * H * P * H).trace + (N * H * N * H).trace := by
    calc
      ((P - N) * H * (P - N) * H).trace =
          (P * H * P * H - P * H * N * H -
            N * H * P * H + N * H * N * H).trace := by
        congr 1
        noncomm_ring
      _ = (P * H * P * H).trace - (P * H * N * H).trace -
          (N * H * P * H).trace + (N * H * N * H).trace := by
        simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [hexpand]
  linarith
