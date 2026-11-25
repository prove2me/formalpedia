-- Prove2me | solution 1 for FiniteEnergyPlane.proj_mem_energySurface
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T11:39:35.02365+00:00
-- url     : https://prove2.me/submissions/7bf40204-7566-4235-8f5c-cbd578cb8d74

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem proj_mem_energySurface_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : proj H y ∈ energySurface H := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 _ hy).exists
  unfold proj scaleToS
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : proj H y ∈ energySurface H :=
  proj_mem_energySurface_aux H hH y hy
