-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.revIn_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.640407+00:00
-- url     : https://prove2.me/submissions/c05555af-346d-47bc-94fb-14ec2f623b0d

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
theorem _root_.solution : ∀ (s : List ℕ) (i j : ℕ), j < s.sum → i < j → blk s i = blk s j →
    revIn s j < revIn s i
  | [], _, _, h, _, _ => by simp at h
  | a :: s, i, j, h, hij, hb => by
    simp only [List.sum_cons] at h
    simp only [blk] at hb
    simp only [revIn]
    split_ifs at hb ⊢ with h1 h2 h2
    · omega
    · omega
    · omega
    · have := solution s (i - a) (j - a) (by omega) (by omega) (by omega); omega
end Formalism.DoubleCosetMeasures.P.Phase
