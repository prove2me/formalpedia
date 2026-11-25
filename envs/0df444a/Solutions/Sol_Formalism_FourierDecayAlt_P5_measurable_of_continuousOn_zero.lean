-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.measurable_of_continuousOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:10:15.147343+00:00
-- url     : https://prove2.me/submissions/e62e8270-c332-4ade-bcf0-26c502ee623e

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero

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
theorem _root_.solution {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) (h0 : ∀ x ∉ s, f x = 0) : Measurable f := by
  classical
  have e : f = s.piecewise f (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx, h0]
  rw [e]
  exact hf.measurable_piecewise continuousOn_const hs
end Formalism.FourierDecayAlt.P5
