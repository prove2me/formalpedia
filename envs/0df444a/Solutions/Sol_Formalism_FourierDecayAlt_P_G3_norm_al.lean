-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.norm_al
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:40.042103+00:00
-- url     : https://prove2.me/submissions/0c67f915-c63d-4aea-9d48-543c08caea23

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (β : ℂ) : ‖al β‖ = ‖β‖ / (2 * Real.pi) := by
  unfold al
  rw [norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl
end Formalism.FourierDecayAlt.P.G3
