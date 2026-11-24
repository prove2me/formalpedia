-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.haarW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:57.070795+00:00
-- url     : https://prove2.me/submissions/213bbc5f-2c2c-4afc-a374-0571d1ef56c0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_compactHaar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_compactW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : HaarWExists := fun k r z hz hT => compactHaar k r _ (closedW k r z) (compactW k r z hz hT)
end Formalism.FourierDecayAlt.P.B2x3
