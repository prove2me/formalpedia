-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.revIn_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:55.195339+00:00
-- url     : https://prove2.me/submissions/297e9230-7271-4ffd-9796-1ca1dbe36d48

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
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j + 1 < s.sum → blk s j = blk s (j + 1) →
    revIn s (j + 1) + 1 = revIn s j
  | [], _, h, _ => by simp at h
  | a :: s, j, h, hb => by
    simp only [List.sum_cons] at h
    simp only [blk] at hb
    simp only [revIn]
    split_ifs at hb ⊢ with h1 h2 h2
    · omega
    · omega
    · omega
    · have e : j + 1 - a = (j - a) + 1 := by omega
      rw [e] at hb ⊢
      have := solution s (j - a) (by omega) (by omega); omega
end Formalism.DoubleCosetMeasures.P.Phase
