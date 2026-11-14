-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_smallnegative_source_cutoff_bands_union_open_negative_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:19:30.760684+00:00
-- url     : https://prove2.me/submissions/8ed3734f-b7db-4ca2-b3d7-84f22808be85

import Mathlib
import Mathlib.Algebra.Order.Archimedean.Real.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
noncomputable section

/-- The increasing genuine compensated mark bands exhaust precisely the strict small-negative marks. -/
theorem solution :
    (⋃ n : ℕ, Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) =
      Ioo (-1 : ℝ) 0 := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨n, hleft, hright⟩
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := div_pos one_pos hd
    exact ⟨hleft, by linarith⟩
  · intro hz
    letI : Archimedean ℝ := Real.instArchimedean
    have hpos : (0 : ℝ) < -z := by linarith [hz.2]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, hz.1, ?_⟩
    linarith
