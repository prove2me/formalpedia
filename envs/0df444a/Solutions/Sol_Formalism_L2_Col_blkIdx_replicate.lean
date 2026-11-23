-- Prove2me | solution 1 for Formalism.L2.Col.blkIdx_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:08.781946+00:00
-- url     : https://prove2.me/submissions/f8b66377-9aa8-451d-a1e9-be55879030a4

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
theorem _root_.solution {t : ℕ} (ht : 0 < t) (j i : ℕ) (h : i < j * t) : blkIdx (List.replicate j t) i = i / t := by
  induction j generalizing i with
  | zero => simp at h
  | succ j ih =>
    rw [List.replicate_succ, blkIdx]
    split_ifs with h1
    · exact (Nat.div_eq_of_lt h1).symm
    · have h2 : i - t < j * t := by
        have : (j + 1) * t = j * t + t := by ring
        omega
      rw [ih _ h2]
      have h3 : i = (i - t) + t := by omega
      conv_rhs => rw [h3, Nat.add_div_right _ ht]
end Formalism.L2.Col
