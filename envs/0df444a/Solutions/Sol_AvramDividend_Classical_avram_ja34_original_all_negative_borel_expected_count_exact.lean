-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja34_original_all_negative_borel_expected_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:26:34.831118+00:00
-- url     : https://prove2.me/submissions/a54d0937-caea-4c65-8fca-f08ba06149ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original negative Borel mark has exact finite-horizon Levy first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
      (T : ℝ≥0∞) * X.ν B := by
  have hSeparated :
      ∀ (C : Set ℝ), MeasurableSet C →
        ∀ ε : ℝ, 0 < ε → C ⊆ Iic (-ε) →
        (∫⁻ ω,
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u, X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C := by
    intro C hC ε hε hCsep
    simpa using
      (avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X 1 C hC ε hε hCsep)
  have hMean :=
    avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
      X hSeparated T B hB
  simpa only [Set.inter_eq_left.mpr hNeg] using hMean
