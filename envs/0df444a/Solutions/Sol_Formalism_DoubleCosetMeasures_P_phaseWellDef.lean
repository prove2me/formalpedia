-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.phaseWellDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:21.5328+00:00
-- url     : https://prove2.me/submissions/571db0e7-9e6c-4425-ade1-72ffddede1cf

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_phase_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.PhaseWellDef := Phase.phase_main
end Formalism.DoubleCosetMeasures.P
