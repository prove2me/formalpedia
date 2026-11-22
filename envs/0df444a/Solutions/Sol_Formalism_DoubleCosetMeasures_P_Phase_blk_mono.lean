-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.blk_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:55.216291+00:00
-- url     : https://prove2.me/submissions/fa753e41-5a9c-4597-8c51-db02b074242e

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock

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
theorem _root_.solution : ∀ (s : List ℕ) (i j : ℕ), i ≤ j → blk s i ≤ blk s j
  | [], _, _, _ => by simp [blk]
  | a :: s, i, j, h => by
    simp only [blk]
    split_ifs with h1 h2 h2
    · exact le_refl _
    · omega
    · omega
    · have := solution s (i - a) (j - a) (by omega); omega
end Formalism.DoubleCosetMeasures.P.Phase
