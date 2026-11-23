-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.boundedSubsequence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:47.839432+00:00
-- url     : https://prove2.me/submissions/d0d5318b-d21c-4df6-9ae0-1dcacb415090

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_boundedSubseq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.BoundedSubseq := A6x2.boundedSubseq
end Formalism.FourierDecayAlt.P
