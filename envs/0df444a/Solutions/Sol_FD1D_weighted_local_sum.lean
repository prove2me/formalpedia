-- Prove2me | solution 1 for FD1D.weighted_local_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:20.997395+00:00
-- url     : https://prove2.me/submissions/7c0567b0-49b5-42e3-b989-855d90bf7b92

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weighted_childAverage_sum

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f (d + 1) - weightedLevel f d := by
  rw [show (∑ v, nodeMass d v * (childAverage f d v - f d v)) =
      (∑ v, nodeMass d v * childAverage f d v) -
        ∑ v, nodeMass d v * f d v by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring]
  rw [weighted_childAverage_sum]
  rfl
end FD1D
