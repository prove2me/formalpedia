-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_horizon_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:23:44.728514+00:00
-- url     : https://prove2.me/submissions/427cb72c-4802-4e9f-9b9e-c1df8e6dd0d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source marked jump count is pathwise monotone in the time horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (B : Set ℝ) (hST : S ≤ T) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX ω (Ioc 0 S ×ˢ B) ≤ NX ω (Ioc 0 T ×ˢ B)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change NX ω (Ioc 0 S ×ˢ B) ≤ NX ω (Ioc 0 T ×ˢ B)
  apply measure_mono
  rintro ⟨u, z⟩ ⟨⟨hu0, huS⟩, hz⟩
  exact ⟨⟨hu0, huS.trans hST⟩, hz⟩
