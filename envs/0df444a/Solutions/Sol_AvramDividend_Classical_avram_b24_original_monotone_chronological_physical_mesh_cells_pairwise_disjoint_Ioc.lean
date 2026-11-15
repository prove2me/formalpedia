-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:46:26.174861+00:00
-- url     : https://prove2.me/submissions/1cd239fa-6349-4ba2-b03d-d8b790076095

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (t : ℕ → ℝ≥0) (hmono : Monotone t)
    (I : Finset ℕ) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Ioc (t i) (t (i + 1)))
        (Ioc (t j) (t (j + 1))) := by
  have hforward (i j : ℕ) (hij : i < j) :
      Disjoint (Ioc (t i) (t (i + 1)))
        (Ioc (t j) (t (j + 1))) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    have hij' : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have hle : t (i + 1) ≤ t j := hmono hij'
    exact (not_lt_of_ge (hu.2.trans hle)) hv.1
  intro i hi j hj hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hforward i j hlt
  · exact (hforward j i hgt).symm
