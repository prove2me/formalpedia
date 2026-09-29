-- Prove2me | solution 1 for Freiman.separated_copies_limit_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:13.824602+00:00
-- url     : https://prove2.me/submissions/71b7d84b-3ca4-4360-9795-7609e79b2e8f

import Definitions.Def_Freiman_wordRealization
import Theorems.Thm_Freiman_separated_copies_limit_classification
import Theorems.Thm_Freiman_localValue_shift
import Theorems.Thm_Freiman_background_unrestricted
import Theorems.Thm_Freiman_separated_copies_avoid
import Theorems.Thm_Freiman_avoid_coordinate_limit
import Theorems.Thm_Freiman_avoid_shift
import Theorems.Thm_Freiman_background_avoiding
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a b : ℤ → ℕ+) (N : ℕ) (t : ℝ)
    (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (hcondition : Real.sqrt 21 ≤ t ∨ (AvoidsBlock a [3, 1, 3, 1, 3] ∧ (4 * Real.sqrt 462 / 19 : ℝ) ≤ t))
    (u : ℕ → ℕ) (hu : StrictMono u) (y : ℤ → ℕ+)
    (hy : CoordinateLimit (fun j i => b ((u j : ℤ) + i)) y) :
    localValue y 0 ≤ t := by
  rcases separated_copies_limit_classification a b N hcopy hfinite u hu y hy with hs | h3
  · obtain ⟨s, hs⟩ := hs
    have heq : y = fun i : ℤ => a (s + i) := funext hs
    rw [heq, localValue_shift, add_zero]
    exact hmax s
  · rcases hcondition with hhigh | ⟨havoid, hthreshold⟩
    · exact (background_unrestricted y h3 0).trans hhigh
    · have hb := separated_copies_avoid a b N hcopy havoid
      have hyavoid := avoid_coordinate_limit (fun j i => b ((u j : ℤ) + i)) y
        [3, 1, 3, 1, 3] (fun j => avoid_shift b _ (u j : ℤ) hb) hy
      exact (background_avoiding y h3 hyavoid 0).trans hthreshold
