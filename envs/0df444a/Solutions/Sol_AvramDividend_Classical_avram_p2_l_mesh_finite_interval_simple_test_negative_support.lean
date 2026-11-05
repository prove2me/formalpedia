-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_interval_simple_test_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:59:13.728845+00:00
-- url     : https://prove2.me/submissions/8bd677dd-d24b-4756-912e-1123c7435c7d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped BigOperators Classical

/-- Every finite linear combination of interval indicators whose upper
endpoints lie below the negative cutoff vanishes above that cutoff. -/
theorem solution {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (ρ : ℝ)
    (hb : ∀ i : ι, b i ≤ -ρ)
    (z : ℝ) (hz : -ρ < z) :
    (∑ i : ι, if z ∈ Ioc (a i) (b i) then c i else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : z ∉ Ioc (a i) (b i) := by
    intro hmem
    have hle : z ≤ b i := hmem.2
    exact (not_le_of_gt hz) (hle.trans (hb i))
  simp only [if_neg hnot]
