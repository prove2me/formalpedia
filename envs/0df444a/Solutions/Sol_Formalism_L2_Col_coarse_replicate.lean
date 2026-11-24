-- Prove2me | solution 1 for Formalism.L2.Col.coarse_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:14.627856+00:00
-- url     : https://prove2.me/submissions/5b544d89-04a8-4f37-91b4-7d5e5248f9bb

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
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {r t j s : ℕ} (ht : 0 < t) (hs : s < j) : coarse r (List.replicate j t) (r + s * t) = s + 1 := by
  unfold coarse
  simp only [blkIdx]
  rw [if_neg (by omega)]
  congr 1
  rw [Nat.add_sub_cancel_left]
  induction s generalizing j with
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [List.replicate_succ, blkIdx, zero_mul, if_pos ht]
  | succ s ih =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul, if_neg (by omega), Nat.add_sub_cancel, ih (by omega)]
end Formalism.L2.Col
