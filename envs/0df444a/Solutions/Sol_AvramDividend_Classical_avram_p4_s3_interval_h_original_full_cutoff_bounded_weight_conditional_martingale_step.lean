-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:31:09.458309+00:00
-- url     : https://prove2.me/submissions/affab395-29bb-48b0-8b7d-806e2cab852e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
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
    let Z : Ω → ℝ := fun ω => H ω * ((N ω).toReal - r)
    MemLp Z 2 P ∧
    (P[Z | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0)) ∧
    (∫ ω, Z ω ∂P) = 0 := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let Z : Ω → ℝ := fun ω => H ω * ((N ω).toReal - r)
  change MemLp Z 2 P ∧
    (P[Z | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0)) ∧
    (∫ ω, Z ω ∂P) = 0
  have hZL2 :=
    avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
      X s T n H hH L hBound
  have hCountSqInt :
      Integrable (fun ω => ((N ω).toReal-r)^2) P :=
    (avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
      X s T n).1
  have hNMeas : Measurable N :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s (s+T) ×ˢ B) (measurableSet_Ioc.prod measurableSet_Iic)
  have hCountSM : AEStronglyMeasurable
      (fun ω => (N ω).toReal-r) P :=
    ((ENNReal.measurable_toReal.comp hNMeas).sub measurable_const).aestronglyMeasurable
  have hCountL2 : MemLp (fun ω => (N ω).toReal-r) 2 P :=
    (memLp_two_iff_integrable_sq hCountSM).2 hCountSqInt
  have hCountInt : Integrable (fun ω => (N ω).toReal-r) P :=
    hCountL2.integrable (by norm_num)
  have hZInt : Integrable Z P :=
    hZL2.integrable (by norm_num)
  have hCountCond :
      P[(fun ω => (N ω).toReal-r) | 𝓕.rightCont s]
        =ᵐ[P] (fun _ => 0) :=
    (avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
      X s T n).1
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := 𝓕.rightCont s) (μ := P)
    (f := H)
    (g := fun ω => (N ω).toReal-r)
    hH hZInt hCountInt
  have hZero : P[Z | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0) := by
    apply hpull.trans
    filter_upwards [hCountCond] with ω hz
    simpa only [Pi.mul_apply, hz, mul_zero]
  refine ⟨hZL2,hZero,?_⟩
  calc
    (∫ ω, Z ω ∂P) =
        ∫ ω, (P[Z | 𝓕.rightCont s]) ω ∂P := by
          symm
          exact integral_condExp (𝓕.rightCont.le s)
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂P := integral_congr_ae hZero
    _ = 0 := by simp
