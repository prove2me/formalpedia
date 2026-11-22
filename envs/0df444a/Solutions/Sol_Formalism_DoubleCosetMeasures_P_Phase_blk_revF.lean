-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.blk_revF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:00.71864+00:00
-- url     : https://prove2.me/submissions/cb4050bb-4dfe-4954-a9a8-52a7aa4813cb

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revIn

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
theorem _root_.solution (s : List ℕ) (a : Fin s.sum) : blk s (revF s a) = blk s a := blk_revIn s a a.2
end Formalism.DoubleCosetMeasures.P.Phase
