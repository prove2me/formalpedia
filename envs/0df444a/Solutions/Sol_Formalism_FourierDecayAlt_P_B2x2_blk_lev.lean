-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.blk_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:53.064354+00:00
-- url     : https://prove2.me/submissions/2c640d92-2498-416c-8ceb-673216d72d1a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm

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
theorem _root_.solution (k r' : ℕ) (x : Mat k r') : blk k r' (ιLev k 1 r' x) = x := by
  ext s t
  simp only [blk, Matrix.of_apply, lev_mm]
end Formalism.FourierDecayAlt.P.B2x2
