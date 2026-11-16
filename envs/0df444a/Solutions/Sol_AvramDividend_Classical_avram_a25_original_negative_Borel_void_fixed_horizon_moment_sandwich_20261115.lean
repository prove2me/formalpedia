-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:51:23.131061+00:00
-- url     : https://prove2.me/submissions/6f4e860a-6df1-4d98-b2dc-410fb97a8735

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original jump-count void is bounded by its source factorial moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
    let deficit : ℝ := 1 - (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B) = 0}).toReal
    r - r ^ 2 / 2 ≤ deficit ∧ deficit ≤ r := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B)
  obtain ⟨K, hK, hCount⟩ :=
    avram_a20_original_negative_borel_nat_count_realisation
      X hFinite s B hB hNeg
  have hFirstS : Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) = ((s : ℝ≥0∞) * X.ν B).toReal :=
    avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite s B hB hNeg
  have hSecondS : Integrable
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) =
        (((s : ℝ≥0∞) * X.ν B).toReal) ^ 2 :=
    avram_ja36_original_negative_borel_cell_factorial_moment
      X hFinite s B hB hNeg
  have hNu : X.ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hFin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 s (show (0 : ℝ≥0) ≤ s from zero_le) B hB hNu
    simpa only [tsub_zero, N] using
      (avram_ja34_original_all_negative_borel_expected_count_exact X s B hB hNeg)
  have hResult :=
    avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
      P N K hK hCount hFin (((s : ℝ≥0∞) * X.ν B).toReal)
      hFirstS hSecondS
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hResult
