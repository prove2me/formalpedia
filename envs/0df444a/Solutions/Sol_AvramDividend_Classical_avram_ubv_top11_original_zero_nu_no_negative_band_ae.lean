-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_original_zero_nu_no_negative_band_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T09:37:11.414687+00:00
-- url     : https://prove2.me/submissions/6ad0a455-88f5-4db2-90a0-5b7dd7e441ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_threshold_iff_leftLim
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_endpoint_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_count_law
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! For zero Lévy jump measure, each original negative-jump band is absent
almost surely on each deterministic finite horizon, using measurable
original marked counts and the exact horizon-endpoint bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNuZero : X.ν = 0)
    (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, ¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Set Ω := {ω : Ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
  have hFm : MeasurableSet F :=
    (𝓕.le T) _
      (avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable X T n)
  have hFmass : P F = 1 := by
    simpa [F, hNuZero] using
      (avram_wave7_06_original_intrinsic_negative_band_zero_count_law X T n)
  have hFae : ∀ᵐ ω ∂P, ω ∈ F :=
    (mem_ae_iff_prob_eq_one hFm).2 hFmass
  filter_upwards [hFae,
      avram_wave7_06_original_negative_band_endpoint_void_ae X T n]
      with ω hF hEnd
  intro ⟨u, hu0, huT, hlim⟩
  have hAll : ∀ v : ℝ≥0, v ∈ Ioc 0 T →
      ¬ (X.X v ω + (1 / ((n : ℝ) + 1)) ≤
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) v) :=
    (avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
      X ω T n).2 hF
  have hOpen : ∀ v : ℝ≥0, 0 < v → v < T →
      ¬ (X.X v ω + (1 / ((n : ℝ) + 1)) ≤
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) v) :=
    hEnd.mpr hAll
  exact (hOpen u hu0 huT)
    ((avram_wave7_06_original_jump_threshold_iff_leftLim
      X ω u hu0 n).1 hlim)
