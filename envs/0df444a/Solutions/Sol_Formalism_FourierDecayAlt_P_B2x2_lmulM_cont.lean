-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lmulM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:47:36.994032+00:00
-- url     : https://prove2.me/submissions/d6bf442f-dbc8-46ca-8d8b-8710f87d5de5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  show Continuous (fun x : Mt k r => (a * Matrix.of x : Mat k r))
  exact continuous_const.matrix_mul hof
end Formalism.FourierDecayAlt.P.B2x2
