-- Prove2me | solution 1 for Formalism.L2.Col.blkIdx_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:21.574807+00:00
-- url     : https://prove2.me/submissions/8e2ca189-bdc8-49ad-a0af-06e332e0d9a1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
namespace Formalism.L2.Col
theorem _root_.solution (bl : List ℕ) : Monotone (blkIdx bl) := by
  induction bl with
  | nil => intro i j _; simp [blkIdx]
  | cons b bs ih =>
    intro i j hij
    simp only [blkIdx]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact Nat.succ_le_succ (ih (by omega))
end Formalism.L2.Col
