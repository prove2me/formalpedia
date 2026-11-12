-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_finite_zero_original_negative_mark_count_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:04:21.116215+00:00
-- url     : https://prove2.me/submissions/18771f09-a07e-4f59-821c-d2e3303cd439

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0 := by
  have hB : MeasurableSet (Iio (0 : ℝ)) := isOpen_Iio.measurableSet
  have hm :=
    AvramDividend.Classical.avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (bot_le : (0 : ℝ≥0) ≤ T) (Iio (0 : ℝ)) hB
  have hE :=
    AvramDividend.Classical.avram_ja34_original_all_negative_borel_expected_count_exact
      X T (Iio (0 : ℝ)) hB (Set.Subset.rfl)
  have hIntegral :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) = 0 := by
    simpa [hZero] using hE
  exact (MeasureTheory.lintegral_eq_zero_iff hm).mp hIntegral
