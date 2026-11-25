-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cyc_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:13.506646+00:00
-- url     : https://prove2.me/submissions/9eadcb6d-c6ce-4b9c-a5ae-7bbc10d92243

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {m : ℕ} (i j : Fin (m + 1)) :
    ((Fin.cycleRange i j : Fin (m + 1)) : ℕ) =
      if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else (j : ℕ) := by
  rcases lt_trichotomy j i with h | h | h
  · rw [Fin.coe_cycleRange_of_lt h, if_pos (show (j : ℕ) < i from h)]
  · subst h; simp
  · rw [Fin.cycleRange_of_gt h, if_neg (by have : (i : ℕ) < j := h; omega),
      if_neg (by have : (i : ℕ) < j := h; omega)]
end Formalism.HermitianLatticeCounting.P
