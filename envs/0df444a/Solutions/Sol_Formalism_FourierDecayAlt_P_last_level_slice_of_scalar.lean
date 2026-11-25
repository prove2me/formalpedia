-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.last_level_slice_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:04.042373+00:00
-- url     : https://prove2.me/submissions/84a7c270-91b4-46db-bb07-8c0bc6535462

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_last_level_slice_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_slice1_of_nnSlice

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
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : NNSlice → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := fun h h23 =>
  last_level_slice_of_parts (slice1_of_nnSlice h) h23
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.JFxDs5
