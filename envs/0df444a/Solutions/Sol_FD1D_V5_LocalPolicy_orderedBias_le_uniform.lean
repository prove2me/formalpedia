-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.orderedBias_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:43.639817+00:00
-- url     : https://prove2.me/submissions/0c225ce2-77e4-421a-bea0-56bc66cd7ddd

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalPolicy
noncomputable section
private theorem orderedBias_eq_caps
    {a p h : ℝ} {x y : ℕ}
    (hxy : y < x) (hy : 0 < y) :
    orderedBias a p h x y =
      min (feedbackCandidate a h x y)
        (min (uniformCandidate h x y) (floorCandidate a p h x y)) := by
  unfold orderedBias
  rw [if_neg (by omega : x ≠ y)]
  rw [if_neg (by omega : x + y ≠ 0)]
  rw [if_neg (by omega : y ≠ 0)]
end
end FD1D.V5.LocalPolicy
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (hxy : y ≤ x) (hy : 0 < y) :
    orderedBias a p h x y ≤ uniformCandidate h x y := by
  by_cases heq : x = y
  · subst x
    simp [orderedBias, uniformCandidate]
  · rw [orderedBias_eq_caps (lt_of_le_of_ne hxy (Ne.symm heq)) hy]
    exact (min_le_right _ _).trans (min_le_left _ _)
end FD1D.V5.LocalPolicy
