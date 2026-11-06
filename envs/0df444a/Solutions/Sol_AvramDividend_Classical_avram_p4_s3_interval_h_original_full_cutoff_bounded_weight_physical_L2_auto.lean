-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:23:29.599759+00:00
-- url     : https://prove2.me/submissions/2206d2da-220d-489c-bcce-65ba43b3bccf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P
  have hCInt : Integrable (fun ω => ((N ω).toReal-r)^2) P :=
    (avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
      X s T n).1
  have hHglobal : Measurable H :=
    hH.measurable.mono (𝓕.rightCont.le s) le_rfl
  have hH2 : AEStronglyMeasurable (fun ω => (H ω)^2) P :=
    ((hHglobal.stronglyMeasurable).pow 2).aestronglyMeasurable
  have hWeightedSM : AEStronglyMeasurable
      (fun ω => (H ω)^2 * ((N ω).toReal-r)^2) P :=
    hH2.mul hCInt.aestronglyMeasurable
  have hMajorInt :
      Integrable (fun ω => L^2 * ((N ω).toReal-r)^2) P :=
    hCInt.const_mul _
  have hWeightedInt :
      Integrable (fun ω => (H ω)^2 * ((N ω).toReal-r)^2) P := by
    apply Integrable.mono hMajorInt hWeightedSM
    exact Filter.Eventually.of_forall (fun ω => by
      have hRange := abs_le.mp (hBound ω)
      have hLeft : 0 ≤ L - H ω := by linarith [hRange.2]
      have hRight : 0 ≤ L + H ω := by linarith [hRange.1]
      have hSq : (H ω)^2 ≤ L^2 := by
        nlinarith [mul_nonneg hLeft hRight]
      have hNonneg : 0 ≤ ((N ω).toReal-r)^2 := sq_nonneg _
      have hx : 0 ≤ (H ω)^2 * ((N ω).toReal-r)^2 :=
        mul_nonneg (sq_nonneg _) hNonneg
      have hy : 0 ≤ L^2 * ((N ω).toReal-r)^2 :=
        mul_nonneg (sq_nonneg _) hNonneg
      simpa only [Real.norm_of_nonneg hx, Real.norm_of_nonneg hy]
        using mul_le_mul_of_nonneg_right hSq hNonneg)
  have hNMeas : Measurable N :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s (s+T) ×ˢ B) (measurableSet_Ioc.prod measurableSet_Iic)
  have hProductSM : AEStronglyMeasurable
      (fun ω => H ω * ((N ω).toReal-r)) P :=
    hHglobal.aestronglyMeasurable.mul
      ((ENNReal.measurable_toReal.comp hNMeas).sub measurable_const).aestronglyMeasurable
  have hProductSq : Integrable
      (fun ω => (H ω * ((N ω).toReal-r))^2) P := by
    convert hWeightedInt using 1
    ext ω
    ring
  exact (memLp_two_iff_integrable_sq hProductSM).2 hProductSq
