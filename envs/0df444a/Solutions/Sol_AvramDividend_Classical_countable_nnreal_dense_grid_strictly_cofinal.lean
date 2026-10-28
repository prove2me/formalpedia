-- Prove2me | solution 1 for AvramDividend.Classical.countable_nnreal_dense_grid_strictly_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:33:43.390109+00:00
-- url     : https://prove2.me/submissions/c9b17097-aeeb-4864-a74e-fdcf8bdc121c

import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Continuous
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-- Density supplies a deterministic grid point between any finite observation
time and any later extended nonnegative stopping horizon. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hDense : DenseRange grid)
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (htσ : (t : ℝ≥0∞) < σ) :
    ∃ n : ℕ, t < grid n ∧ (grid n : ℝ≥0∞) < σ := by
  obtain ⟨u, htu, huσ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp htσ
  have htu' : t < u := by exact_mod_cast htu
  obtain ⟨v, htv, hvu⟩ := exists_between htu'
  obtain ⟨n, hn⟩ :=
    hDense.exists_mem_open isOpen_Ioo ⟨v, htv, hvu⟩
  have hnu : grid n < u := hn.2
  have hnu' : (grid n : ℝ≥0∞) < (u : ℝ≥0∞) := by
    exact_mod_cast hnu
  exact ⟨n, hn.1, hnu'.trans huσ⟩