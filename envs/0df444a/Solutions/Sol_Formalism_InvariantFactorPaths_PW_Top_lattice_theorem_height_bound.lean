-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:46.929353+00:00
-- url     : https://prove2.me/submissions/25fa3238-7f19-47ee-b157-f7547d79c730

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeTheoremOfDischarge
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Theorems.Thm_Formalism_CountingSumsFrames_Top_theoremM
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_discharge_height_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lattice_theorem_of_discharge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.PW.Top
namespace Formalism.InvariantFactorPaths.PW.Top
theorem _root_.solution : LatticeTheoremHeightBound := lattice_theorem_of_discharge Formalism.CountingSumsFrames.Top.theoremM discharge_height_bound
end Formalism.InvariantFactorPaths.PW.Top
