-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:42:58.662269+00:00
-- url     : https://prove2.me/submissions/b3fec81a-8f7d-4a29-b72d-932a2b820e95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original negative-band zero-count event at horizon zero is the whole sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω |
       NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
       P Set.univ) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω |
      NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ
        Iic (-(1 / ((n : ℝ) + 1)))) = 0} = P Set.univ
  have hEmpty :
      Ioc (0 : ℝ≥0) 0 ×ˢ Iic (-(1 / ((n : ℝ) + 1))) = ∅ := by
    simp
  simp [hEmpty]
