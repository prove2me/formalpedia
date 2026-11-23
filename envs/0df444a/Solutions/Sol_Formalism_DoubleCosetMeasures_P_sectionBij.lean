-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.sectionBij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:38.814436+00:00
-- url     : https://prove2.me/submissions/931469d9-ca63-41ec-b7ce-e0190cbb16a6

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_main

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
theorem _root_.solution : Formalism.DoubleCosetMeasures.SectionBij := Phase.section_main
end Formalism.DoubleCosetMeasures.P
