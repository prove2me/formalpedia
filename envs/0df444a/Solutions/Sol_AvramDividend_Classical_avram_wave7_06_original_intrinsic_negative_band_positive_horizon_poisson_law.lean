-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:18.811212+00:00
-- url     : https://prove2.me/submissions/96e3dfaa-27d2-4ac1-9ba0-33839ebae434

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_real_void_semigroup_exp_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original positive-horizon void law reduced to its true infinitesimal intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by
  classical
  let pE : ℝ≥0 → ENNReal := fun s =>
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  let p : ℝ≥0 → ℝ := fun s => (pE s).toReal
  have hPower : ∀ k : ℕ, 0 < k →
      p T = (p (T / (k : ℝ≥0))) ^ k := by
    intro k hk
    have hkne : (k : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    have htime : (k : ℝ≥0) * (T / (k : ℝ≥0)) = T := by
      field_simp [hkne]
    have hp :=
      avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
        X (T / (k : ℝ≥0)) n k
    change pE ((k : ℝ≥0) * (T / (k : ℝ≥0))) =
      (pE (T / (k : ℝ≥0))) ^ k at hp
    rw [htime] at hp
    have hr := congrArg ENNReal.toReal hp
    simpa only [p, ENNReal.toReal_pow] using hr
  have hSlope : Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * (1 - p (T / (k : ℝ≥0))))
      Filter.atTop
      (nhds ((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by
    simpa only [p, pE] using
      (avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
        X T n hT)
  have hexp :=
    avram_wave7_06_real_void_semigroup_exp_limit
      p T (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
      hPower hSlope
  have hfinite : pE T ≠ ⊤ := by
    letI : IsProbabilityMeasure P := X.isProbability
    have hle : pE T ≤ 1 := by
      calc
        pE T ≤ P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    exact ne_top_of_le_ne_top (by simp) hle
  change pE T = ENNReal.ofReal
    (Real.exp (-((T : ℝ) *
      (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))
  calc
    pE T = ENNReal.ofReal (p T) :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν
          (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by
      rw [hexp]
