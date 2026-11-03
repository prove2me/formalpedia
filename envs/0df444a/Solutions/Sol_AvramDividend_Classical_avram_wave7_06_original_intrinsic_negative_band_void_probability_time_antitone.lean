-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_time_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:42:01.161198+00:00
-- url     : https://prove2.me/submissions/98565365-4f94-4539-9bcd-82369ef06fdd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Increasing the physical observation horizon can only decrease the
probability of seeing no actual source negative-band jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} ≤
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hTS : T ≤ T + S :=
    le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ S)
  have hRect : (Ioc 0 T ×ˢ B : Set (ℝ≥0 × ℝ)) ⊆
      Ioc 0 (T + S) ×ˢ B := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨⟨hu.1, hu.2.trans hTS⟩, hz⟩
  have hSub : {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} ⊆
      {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
    intro ω hZero
    have hLe : NX ω (Ioc 0 T ×ˢ B) ≤
        NX ω (Ioc 0 (T + S) ×ˢ B) := measure_mono hRect
    rw [hZero] at hLe
    exact le_antisymm hLe bot_le
  change P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} ≤
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0}
  exact measure_mono hSub
