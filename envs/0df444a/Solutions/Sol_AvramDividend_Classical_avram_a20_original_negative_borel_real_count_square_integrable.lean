-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_real_count_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:19:03.047533+00:00
-- url     : https://prove2.me/submissions/ea4b13ce-b94d-4531-b3dd-781ea1827f18

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => ((N ω).toReal) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : Set ℝ → Ω → ℝ≥0∞ := fun C ω => NX ω (Ioc 0 T ×ˢ C)
  change Integrable (fun ω => (N B ω).toReal ^ 2) P
  have hWhole : Integrable (fun ω => (N (Iio (0 : ℝ)) ω).toReal ^ 2) P := by
    simpa only [N, NX] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFinite T).1
  have hWholeFin : ∀ᵐ ω ∂P, N (Iio (0 : ℝ)) ω < ⊤ := by
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) (Iio (0 : ℝ))
      isOpen_Iio.measurableSet (lt_top_iff_ne_top.mpr hFinite)
    simpa only [tsub_zero] using
      (avram_ja34_original_all_negative_borel_expected_count_exact
        X T (Iio (0 : ℝ)) isOpen_Iio.measurableSet Subset.rfl)
  have hMeas : Measurable (fun ω => (N B ω).toReal) := by
    simpa only [N, NX, zero_add] using
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X 0 T B hB).ennreal_toReal
  have hSqMeas : AEStronglyMeasurable
      (fun ω => (N B ω).toReal ^ 2) P :=
    (hMeas.pow_const 2).aestronglyMeasurable
  apply Integrable.mono' hWhole hSqMeas
  filter_upwards [hWholeFin] with ω hfin
  have hIncl : Ioc 0 T ×ˢ B ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) := by
    intro p hp
    exact ⟨hp.1, hNeg hp.2⟩
  have hLe : (N B ω).toReal ≤ (N (Iio (0 : ℝ)) ω).toReal :=
    ENNReal.toReal_mono (ne_of_lt hfin) (measure_mono hIncl)
  have hN1 : 0 ≤ (N B ω).toReal := ENNReal.toReal_nonneg
  have hN2 : 0 ≤ (N (Iio (0 : ℝ)) ω).toReal := ENNReal.toReal_nonneg
  have hSq : (N B ω).toReal ^ 2 ≤
      (N (Iio (0 : ℝ)) ω).toReal ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLe) (add_nonneg hN1 hN2)]
  have hP : 0 ≤ (N B ω).toReal ^ 2 := sq_nonneg _
  have hW : 0 ≤ (N (Iio (0 : ℝ)) ω).toReal ^ 2 := sq_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hP, abs_of_nonneg hW] using hSq
