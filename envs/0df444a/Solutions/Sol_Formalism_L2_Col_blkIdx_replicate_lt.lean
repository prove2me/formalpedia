-- Prove2me | solution 1 for Formalism.L2.Col.blkIdx_replicate_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:14.385264+00:00
-- url     : https://prove2.me/submissions/0cebdaea-e72d-4a72-b21e-6e213557e5f5

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
theorem _root_.solution (t j i : ℕ) (h : i < j * t) : blkIdx (List.replicate j t) i < j := by
  induction j generalizing i with
  | zero => simp at h
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    split_ifs with hit
    · omega
    · have := ih (i - t) (by omega)
      omega
end Formalism.L2.Col
