-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.blk_lt_of_lt_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:19.03686+00:00
-- url     : https://prove2.me/submissions/87d18b1c-ddbf-4b30-bfd1-6e00d3044a66

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_mono

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
theorem _root_.solution (s : List ℕ) {a c : Fin s.sum} (h : a < c) (hb : blk s a ≠ blk s c) :
    blk s a < blk s c := lt_of_le_of_ne (blk_mono s a c (le_of_lt h)) hb
end Formalism.DoubleCosetMeasures.P.Phase
