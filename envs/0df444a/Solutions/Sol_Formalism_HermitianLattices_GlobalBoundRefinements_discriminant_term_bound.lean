-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.discriminant_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:44.594733+00:00
-- url     : https://prove2.me/submissions/f2e603d4-865c-4e93-b63f-6275931c8d74

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
theorem _root_.solution : DiscriminantTermBound := by
  intro k m L vE hm hmk hpi hL
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast le_trans hm hmk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hvE : 0 < vE := lt_of_lt_of_le Real.pi_pos hpi
  have hlog2v : Real.log (2 * vE) = Real.log 2 + Real.log vE := Real.log_mul (by norm_num) hvE.ne'
  have hlogpos : 0 ≤ Real.log (2 * vE) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have ha0 : 0 ≤ ((m : ℝ) - 1) / (2 * k) := div_nonneg (by linarith) (by linarith)
  have ha1 : ((m : ℝ) - 1) / (2 * k) ≤ 1 / 2 := by
    first
    | rw [div_le_iff₀ (by linarith)]
    | rw [div_le_iff (by linarith)]
    linarith
  constructor
  · have h1 : ((m : ℝ) - 1) / (2 * k) * Real.log (2 * vE) ≤ 1 / 2 * Real.log (2 * vE) :=
      mul_le_mul_of_nonneg_right ha1 hlogpos
    rw [neg_mul]
    linarith
  · rw [neg_mul]
    linarith [mul_nonneg ha0 hlogpos]
end Formalism.HermitianLattices.GlobalBoundRefinements
