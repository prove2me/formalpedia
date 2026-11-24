-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.triangular_sum_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:39.39282+00:00
-- url     : https://prove2.me/submissions/6930b343-0ff7-4cd0-907f-7ac9b9a0d410

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : TriangularSumExponentBound := by
  intro m nT t f N sumW e1 he
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 : (m : ℝ) * e1 ≤ (m : ℝ) * (2 * sumW + f * N) := mul_le_mul_of_nonneg_left he hm
  have h3 : (m : ℝ) * (2 * sumW + f * N + nT * (t + 1) * ((m : ℝ) + 1) / 4)
      = (m : ℝ) * (2 * sumW + f * N) + nT * ((t + 1) / 2) * ((m : ℝ) * (m + 1) / 2) := by ring
  linarith [h2, h3]
end Formalism.HermitianLattices.GlobalBoundRefinements
