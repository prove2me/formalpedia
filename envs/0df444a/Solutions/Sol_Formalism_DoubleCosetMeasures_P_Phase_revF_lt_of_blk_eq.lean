-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:31.726611+00:00
-- url     : https://prove2.me/submissions/5ff24972-3fbb-4327-9200-8b48b98d6c24

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revIn_anti

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
open Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) {a c : Fin s.sum} (hb : blk s a = blk s c) (h : a < c) :
    revF s c < revF s a := revIn_anti s a c c.2 h hb
end Formalism.DoubleCosetMeasures.P.Phase
