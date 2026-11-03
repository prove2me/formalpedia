-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_arbitrary_mark_void_probability_horizon_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:26:24.860502+00:00
-- url     : https://prove2.me/submissions/c85c8f91-2856-432b-afc0-ed94e91e9496

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An actual source marked-void event can only shrink with the observation horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S T : ℝ≥0) (B : Set ℝ) (hST : S ≤ T) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} ≤
     P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0}) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} ≤
    P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0}
  apply measure_mono
  intro ω hω
  have hInclusion : Ioc 0 S ×ˢ B ⊆ Ioc 0 T ×ˢ B := by
    rintro ⟨u, z⟩ ⟨⟨hu0, huS⟩, hz⟩
    exact ⟨⟨hu0, huS.trans hST⟩, hz⟩
  have hCount :
      NX ω (Ioc 0 S ×ˢ B) ≤ NX ω (Ioc 0 T ×ˢ B) :=
    measure_mono hInclusion
  have hBound : NX ω (Ioc 0 S ×ˢ B) ≤ 0 := by
    calc
      NX ω (Ioc 0 S ×ˢ B) ≤ NX ω (Ioc 0 T ×ˢ B) := hCount
      _ = 0 := hω
  exact le_antisymm hBound bot_le
