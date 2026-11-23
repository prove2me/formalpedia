-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:43.067979+00:00
-- url     : https://prove2.me/submissions/1fc6842e-f98b-4cc2-ac00-1dc0112f0615

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revIn
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
theorem _root_.solution (s : List ℕ) {a c : Fin s.sum} (hb : blk s a < blk s c) :
    revF s a < revF s c := by
  show revIn s a < revIn s c
  by_contra hcon
  have := blk_mono s (revIn s c) (revIn s a) (by omega)
  rw [blk_revIn s c c.2, blk_revIn s a a.2] at this
  omega
end Formalism.DoubleCosetMeasures.P.Phase
