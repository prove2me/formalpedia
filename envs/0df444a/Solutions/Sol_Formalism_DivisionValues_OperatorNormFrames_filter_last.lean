-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.filter_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:11.906042+00:00
-- url     : https://prove2.me/submissions/68aa3b93-fe5d-4d24-abc8-76695a98b574

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm

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
theorem _root_.solution {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < Fin.last m) = Finset.univ := by
  first
    | exact Finset.filter_true_of_mem fun i _ => Fin.castSucc_lt_last i
    | ext i; simp [Fin.castSucc_lt_last]
end Formalism.DivisionValues.OperatorNormFrames
