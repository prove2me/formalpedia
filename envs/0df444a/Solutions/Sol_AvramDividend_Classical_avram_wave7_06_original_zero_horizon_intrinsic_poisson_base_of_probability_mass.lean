-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_of_probability_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:49:16.00461+00:00
-- url     : https://prove2.me/submissions/0b238d53-c14e-41d2-997b-7ef10f46b6bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original Poisson zero-count boundary formula at T=0, under explicit P normalisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (hP : P Set.univ = 1) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω |
       NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
       ENNReal.ofReal (Real.exp
         (-((0 : ℝ) *
           (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω |
      NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ
        Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    ENNReal.ofReal (Real.exp
      (-((0 : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))
  have hEmpty :
      Ioc (0 : ℝ≥0) 0 ×ˢ Iic (-(1 / ((n : ℝ) + 1))) = ∅ := by
    simp
  simp [hEmpty, hP]
