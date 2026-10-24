-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_energy_nonneg_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:48:45.904108+00:00
-- url     : https://prove2.me/submissions/140d7300-7a9a-48f7-b042-a84807d956f2

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
omit [Fintype ι] [DecidableEq ι] in
/-- For real matrices, positive semidefiniteness entails symmetry. -/
private theorem FunctionalInequalities.Analysis.real_posSemidef_isSymm {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.IsSymm := by
  change A.transpose = A
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA.isHermitian.eq
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A positive semidefinite weight makes the trace energy of every symmetric
real matrix nonnegative. -/
theorem solution {B H : Matrix ι ι ℝ}
    (hB : B.IsSymm) (hH : H.PosSemidef) :
    0 ≤ (B * H * B * H).trace := by
  have hHs : H.IsSymm := real_posSemidef_isSymm hH
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  have hX' : H = X.conjTranspose * X := by
    simpa only [Matrix.star_eq_conjTranspose] using hX
  let C : Matrix ι ι ℝ := X * B * X.conjTranspose
  have hC : C.IsSymm := by
    change C.transpose = C
    simp [C, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.mul_assoc, hB.eq]
  have hCpsd : (C * C).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hC.eq] using
      (Matrix.posSemidef_conjTranspose_mul_self C)
  have heq : (B * H * B * H).trace = (C * C).trace := by
    calc
      (B * H * B * H).trace =
          (B * (X.conjTranspose * X) * B *
            (X.conjTranspose * X)).trace := by rw [hX']
      _ = (X * (B * X.conjTranspose * X * B * X.conjTranspose)).trace := by
        simpa [Matrix.mul_assoc] using
          (Matrix.trace_mul_comm
            (B * X.conjTranspose * X * B * X.conjTranspose) X)
      _ = (C * C).trace := by simp [C, Matrix.mul_assoc]
  rw [heq]
  exact hCpsd.trace_nonneg
