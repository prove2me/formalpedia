-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.weighted_L2_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:15.606644+00:00
-- url     : https://prove2.me/submissions/506dc7e1-b4ad-41bb-bdd5-de5763e8d606

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) : WeightedL2 B wt (fun _ => 0) := by
  unfold WeightedL2
  refine ⟨aestronglyMeasurable_const, ?_⟩
  simp
end Formalism.FourierDecayAlt.P.LEx1
