-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_eventually_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:03:05.883948+00:00
-- url     : https://prove2.me/submissions/0befb099-5de3-46bb-86aa-7e328fe6d91f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_band_no_early_source_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_mark_band_void_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original separated negative-band count vanishes on a path-dependent initial clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ T : ℝ≥0, T < ε →
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
  classical
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε, hEarly⟩ :=
    avram_wave7_06_original_separated_band_no_early_source_jumps X ω n
  refine ⟨ε, hε, ?_⟩
  intro T hT
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hBneg : Iic (-δ) ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hneg : -δ < (0 : ℝ) := by linarith
    exact lt_of_le_of_lt hz hneg
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u : ℝ≥0 => (u, j u))) (Ioc 0 T ×ˢ Iic (-δ)) = 0
  apply (avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
    X ω T (Iic (-δ)) measurableSet_Iic hBneg).1
  intro u hu
  have huε : u < ε := lt_of_le_of_lt hu.2 hT
  have hSmall : dist (j u) 0 < δ := by
    simpa only [j, δ] using hEarly u hu.1 huε
  intro hzB
  have hAbs : |j u| < δ := by simpa [Real.dist_eq] using hSmall
  have hLow : -δ < j u := (abs_lt.mp hAbs).1
  exact (not_lt_of_ge hzB) hLow
