-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.topDensMeasAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:43.435991+00:00
-- url     : https://prove2.me/submissions/c2d11dff-4bbd-4b69-a209-cf6cd2af5986

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pair_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : TopDensMeasAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K w u v _ _ c
  refine Measurable.stronglyMeasurable ?_
  unfold topDens
  exact Finset.measurable_sum _ fun e _ => pair_measurable c _ _
end Formalism.FourierDecayAlt.P5
