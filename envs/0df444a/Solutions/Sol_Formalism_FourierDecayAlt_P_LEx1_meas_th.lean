-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.meas_th
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:13.59472+00:00
-- url     : https://prove2.me/submissions/2d761281-ac6f-4d59-a33e-bb1da6133e03

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
theorem _root_.solution (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := by
  unfold th
  exact (B.G_meas.div (B.G_meas.add_const ε)).pow_const σ
end Formalism.FourierDecayAlt.P.LEx1
