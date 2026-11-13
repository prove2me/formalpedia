-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva85_original_marked_jump_measure_zero_initial_fibre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:32:04.776434+00:00
-- url     : https://prove2.me/submissions/dafa97de-a012-48f2-a0c2-723ed9ed516f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (({0} : Set ℝ≥0) ×ˢ Set.univ) = 0 := by
  have hSet : MeasurableSet (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set ℝ)) := by
    measurability
  rw [Measure.map_apply hMeas hSet]
  have hPre :
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ⁻¹'
        (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set ℝ)) =
      ({0} : Set ℝ≥0) := by
    ext u
    simp
  rw [hPre]
  exact avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock X ω
