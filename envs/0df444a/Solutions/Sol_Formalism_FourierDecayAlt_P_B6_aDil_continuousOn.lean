-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.aDil_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:54.626808+00:00
-- url     : https://prove2.me/submissions/99c8ae02-d15c-4c1c-82aa-a6b6f312cf0a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (k r : ℕ) : ContinuousOn (fun t : ℝ => aDil k r t) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  unfold aDil
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  show Continuous fun t : Set.Ioi (0 : ℝ) => if i.val < r then (((t : ℝ) ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else ((((t : ℝ) ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)
  split_ifs
  · exact Complex.continuous_ofReal.comp (continuous_subtype_val.pow _)
  · exact continuous_const
  · refine Complex.continuous_ofReal.comp (Continuous.inv₀ (continuous_subtype_val.pow _) ?_)
    intro t
    exact pow_ne_zero _ (ne_of_gt t.2)
end Formalism.FourierDecayAlt.P.B6
