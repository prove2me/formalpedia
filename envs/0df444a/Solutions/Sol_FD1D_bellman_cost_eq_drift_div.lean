-- Prove2me | solution 1 for FD1D.bellman_cost_eq_drift_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:54.926701+00:00
-- url     : https://prove2.me/submissions/a7ebebfb-8bdb-4b6c-b211-8ab83399754a

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) (a : ℝ)
    (N q t Z : ∀ d, DyadicNode d → ℝ)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a)) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L =
      bellmanDrift L a N q / a := by
  simp_rw [nonrootWeightedSum, weightedLevel, bellmanDrift, ht, hZ,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro v _
  ring
end FD1D
