-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_weighted_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:20:50.762006+00:00
-- url     : https://prove2.me/submissions/ede1da87-3fce-426a-b07d-a1ac820604bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
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
    (hWeightedSqInt : Integrable
      (fun ω =>
        (H ω)^2 *
          (((((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal) -
            ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)^2) P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
    r * ∫ ω, (H ω) ^ 2 ∂P
  have hSqInt : Integrable (fun ω => ((N ω).toReal - r)^2) P :=
    (avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
      X s T n).1
  have hSecond :
      P[(fun ω => ((N ω).toReal - r)^2) | 𝓕.rightCont s]
        =ᵐ[P] fun _ => r :=
    (avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
      X s T n).2
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := 𝓕.rightCont s) (μ := P)
    (f := fun ω => (H ω)^2)
    (g := fun ω => ((N ω).toReal-r)^2)
    (hH.pow 2) hWeightedSqInt hSqInt
  have hcond : P[(fun ω => (H ω)^2 * ((N ω).toReal - r)^2)
      | 𝓕.rightCont s] =ᵐ[P] (fun ω => (H ω)^2 * r) := by
    apply hpull.trans
    filter_upwards [hSecond] with ω hz
    simpa only [Pi.mul_apply, hz]
  calc
    (∫ ω, (H ω * ((N ω).toReal-r))^2 ∂P) =
        ∫ ω, (H ω)^2 * ((N ω).toReal-r)^2 ∂P := by
          congr 1
          funext ω
          ring
    _ = ∫ ω, (P[(fun ω => (H ω)^2 *
          ((N ω).toReal-r)^2) | 𝓕.rightCont s]) ω ∂P := by
          symm
          exact integral_condExp (𝓕.rightCont.le s)
    _ = ∫ ω, (H ω)^2 * r ∂P := integral_congr_ae hcond
    _ = r * ∫ ω, (H ω)^2 ∂P := by
          rw [integral_mul_const]
          ring
