-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_weighted_indicator_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:46:33.113544+00:00
-- url     : https://prove2.me/submissions/8de82642-356b-40e0-92e9-c5bafa4fc26d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped BigOperators Classical

/-- A finite real-weighted indicator sum equals the cardinality of the
marked subcollection times the common weight. -/
theorem solution {α : Type*} [DecidableEq α]
    (s : Finset α) (v : α → ℝ) (B : Set ℝ) (c : ℝ) :
    (∑ x ∈ s, if v x ∈ B then c else 0) =
      ((s.filter (fun x => v x ∈ B)).card : ℝ) * c := by
  classical
  calc
    _ = ∑ x ∈ s.filter (fun x => v x ∈ B), c := by
      rw [Finset.sum_filter]
    _ = _ := by simp
