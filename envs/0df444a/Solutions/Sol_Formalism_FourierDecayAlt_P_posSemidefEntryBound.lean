-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.posSemidefEntryBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:25.050522+00:00
-- url     : https://prove2.me/submissions/db871b75-3dff-4f90-8aae-eefa1d1cd5a7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_pSDEntryBound

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
theorem _root_.solution : Formalism.FourierDecayAlt.A6.PSDEntryBound := A6x2.pSDEntryBound
end Formalism.FourierDecayAlt.P
