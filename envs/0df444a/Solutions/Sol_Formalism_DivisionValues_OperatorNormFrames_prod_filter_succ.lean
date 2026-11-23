-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.prod_filter_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:01.033803+00:00
-- url     : https://prove2.me/submissions/2bae0774-cf43-45e8-9925-b4219931c0d3

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_succ

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
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {m : ℕ} (k : Fin m → ℝ) (j : Fin m) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ), k i =
      k j * ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc), k i := by
  rw [filter_succ, Finset.prod_insert (by simp)]
end Formalism.DivisionValues.OperatorNormFrames
