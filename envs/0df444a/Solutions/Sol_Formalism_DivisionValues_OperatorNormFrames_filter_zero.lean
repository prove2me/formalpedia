-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.filter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:46.626845+00:00
-- url     : https://prove2.me/submissions/7a730ac5-3253-4c88-b178-2ce9a97a1465

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
    Finset.univ.filter (fun i : Fin m => i.castSucc < (0 : Fin (m + 1))) = ∅ := by
  first
    | exact Finset.filter_false_of_mem fun i _ => Fin.not_lt_zero _
    | ext i; simp
end Formalism.DivisionValues.OperatorNormFrames
