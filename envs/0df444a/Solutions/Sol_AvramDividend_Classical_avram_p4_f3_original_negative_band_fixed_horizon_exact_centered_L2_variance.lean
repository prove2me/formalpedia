-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_band_fixed_horizon_exact_centered_L2_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:29:29.601229+00:00
-- url     : https://prove2.me/submissions/c49ab3e5-5aba-4187-bdb8-63cbc5cdf442

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_mean_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_count_l2_pair_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual original fixed-horizon negative-band count has exact centred L² variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
      (∫ ω, (J ω - r) ^ 2 ∂P) = r := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  let B : Set ℝ := Iic (-ε)
  let J : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)).toReal
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hBm : MeasurableSet B := measurableSet_Iic
  have hBsep : B ⊆ Iic (-ε) := Subset.rfl
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hBm ε hε hBsep
  have hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * X.ν B :=
    avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X T B hBm ε hε hBsep
  have hJmean : (∫ ω, J ω ∂P) = r := by
    have hRawMean := avram_p2_e_compensator_finite_nu_count_real_mean
      X 0 T (by simp) B hBm hν (by simpa using hRate)
    simpa only [J, r, tsub_zero] using hRawMean
  have hJi : Integrable J P :=
    avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  have hPair := avram_p4_f_assembly_original_chronological_pair_mean_exact
    X T n
  exact avram_p4_f_assembly_original_centered_count_l2_pair_rate
    X T n hJi hJmean hPair.1 hPair.2
