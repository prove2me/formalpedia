-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.cont_detM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:07.64052+00:00
-- url     : https://prove2.me/submissions/59fe2bb6-ef6f-4b0e-a869-abff8b096536

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
theorem _root_.solution (s : ℕ) : Continuous (detM : Mat s → ℂ) := by
  unfold detM
  exact Continuous.matrix_det (A := fun Z : Mat s => Matrix.of Z) continuous_id
end Formalism.FourierDecayAlt.P.G3
