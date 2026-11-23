-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.cnorm_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:16.727281+00:00
-- url     : https://prove2.me/submissions/85d64e72-6351-4131-9baa-1df36a8c624a

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
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n : ℕ} (u : Fin n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (star u) = Formalism.HermitianLatticesTheory.cnorm u := by
  first
    | simp [Formalism.HermitianLatticesTheory.cnorm, norm_star]
    | simp [Formalism.HermitianLatticesTheory.cnorm, Complex.norm_conj]
end Formalism.DivisionValues.OperatorNormFrames
