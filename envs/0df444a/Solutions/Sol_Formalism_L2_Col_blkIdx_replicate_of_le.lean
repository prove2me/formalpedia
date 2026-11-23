-- Prove2me | solution 1 for Formalism.L2.Col.blkIdx_replicate_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:54.529079+00:00
-- url     : https://prove2.me/submissions/71c815c0-7704-4160-b896-151875363a0c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

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
theorem _root_.solution (t j i : ℕ) (h : j * t ≤ i) : blkIdx (List.replicate j t) i = j := by
  induction j generalizing i with
  | zero => simp only [List.replicate_zero, blkIdx]
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    rw [if_neg (by omega), ih (i - t) (by omega)]
end Formalism.L2.Col
