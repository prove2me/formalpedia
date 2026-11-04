-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_positive_from_short_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:56:03.985197+00:00
-- url     : https://prove2.me/submissions/1c1968e8-9d52-457e-b908-5f9d7865d498

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Positivity at a source subdivided interval propagates across the actual void semigroup. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n k : ℕ) :
    (let p : ℝ≥0 → ENNReal := fun s =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
     0 < (p (T / ((k + 1 : ℕ) : ℝ≥0))).toReal →
       0 < (p T).toReal) := by
  classical
  let p : ℝ≥0 → ENNReal := fun s =>
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  change 0 < (p (T / ((k + 1 : ℕ) : ℝ≥0))).toReal →
    0 < (p T).toReal
  intro hShort
  have hkne : ((k + 1 : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have htime : ((k + 1 : ℕ) : ℝ≥0) *
      (T / ((k + 1 : ℕ) : ℝ≥0)) = T := by
    field_simp [hkne]
  have hp :=
    avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
      X (T / ((k + 1 : ℕ) : ℝ≥0)) n (k + 1)
  change p (((k + 1 : ℕ) : ℝ≥0) *
      (T / ((k + 1 : ℕ) : ℝ≥0))) =
    (p (T / ((k + 1 : ℕ) : ℝ≥0))) ^ (k + 1) at hp
  rw [htime] at hp
  have hr := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_pow] at hr
  rw [hr]
  exact pow_pos hShort _
