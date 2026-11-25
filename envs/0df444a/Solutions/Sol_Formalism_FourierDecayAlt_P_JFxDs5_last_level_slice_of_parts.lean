-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs5.last_level_slice_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:10.306649+00:00
-- url     : https://prove2.me/submissions/8742d674-86e0-4bb3-b7f2-4b4bf98ea3c5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxDs5
theorem _root_.solution : Slice1 → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := by
  intro h1 h23 k r Wp Wq _ _ _ _ _ _ D A m F hThr hF
  exact ⟨h1 k r Wp Wq D A m F hThr hF, (h23 k r Wp Wq D A m F hThr hF).1, (h23 k r Wp Wq D A m F hThr hF).2⟩
end Formalism.FourierDecayAlt.P.JFxDs5
