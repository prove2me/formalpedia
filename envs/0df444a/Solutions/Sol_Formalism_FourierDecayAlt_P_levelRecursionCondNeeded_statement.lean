-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.levelRecursionCondNeeded_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:46:07.622941+00:00
-- url     : https://prove2.me/submissions/af9d2ebd-e8d8-4dae-ac05-c6308139b638

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LevelRecursionCondNeeded := by
  intro h
  have := h 2 (1/3) 0 (fun _ => 0) (fun i => (4/3 : ℝ) ^ i) (by norm_num) le_rfl (by norm_num)
    (fun _ => le_rfl) (fun _ => by norm_num) (fun i => by positivity)
    (by
      intro i h1 _
      have : ∑ s ∈ Icc 2 i, (0:ℝ) ^ (s - 1) * (4/3 : ℝ) ^ (i - s) = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have : s - 1 ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
        simp [this]
      rw [this]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp [pow_succ]; linarith [pow_pos (show (0:ℝ) < 4/3 by norm_num) k])
    (by norm_num)
  norm_num at this
end Formalism.FourierDecayAlt.P
