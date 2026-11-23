-- Prove2me | solution 1 for Formalism.DivisionValues.composition_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:14.688817+00:00
-- url     : https://prove2.me/submissions/dc739422-d16a-490a-bee2-1b43cd5aa6c7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_prod_filter_succ
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_last
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : CompNorm := by
  unfold CompNorm
  intro m C _ Kj k hk hK φ
  have key : ∀ i : Fin (m + 1), ‖chainFun Kj i φ‖ ≤
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => j.castSucc < i), k j) * ‖φ‖ := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have h0 : chainFun Kj 0 φ = φ := by first | rfl | simp [chainFun]
      simp only [h0, filter_zero, Finset.prod_empty, one_mul, le_refl]
    | succ j ih =>
      have h1 : chainFun Kj j.succ φ = Kj j (chainFun Kj j.castSucc φ) := by
        first | rfl | simp [chainFun]
      rw [prod_filter_succ, h1, mul_assoc]
      exact (hK j _).trans (mul_le_mul_of_nonneg_left ih (hk j))
  simpa only [filter_last] using key (Fin.last m)
end Formalism.DivisionValues
