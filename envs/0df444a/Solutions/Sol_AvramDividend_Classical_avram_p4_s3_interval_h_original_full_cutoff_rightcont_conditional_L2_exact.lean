-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:13:40.977145+00:00
-- url     : https://prove2.me/submissions/6ad3a15d-c769-432e-b2f7-53c338e395d5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => r)) := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s (s + T) ×ˢ B)
  let N0 : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => r))
  have hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
    intro ω
    rfl
  have hL2Origin : MemLp (fun ω => (N0 ω).toReal - r) 2 P := by
    simpa only [N0, NX, B, r, tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T n 0 T (zero_le : 0 ≤ T) le_rfl B measurableSet_Iic (Subset.rfl))
  have hN0I : Integrable (fun ω => (N0 ω).toReal) P := by
    have h := (hL2Origin.integrable (by norm_num)).add (integrable_const r)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [Pi.add_apply]))
  have hNShift :=
    avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
      X NX hNX s T B measurableSet_Iic
      (fun z : ℝ≥0∞ => z.toReal) ENNReal.measurable_toReal hN0I
  have hMean0 : (∫ ω, (N0 ω).toReal ∂P) = r := by
    simpa only [N0, NX, B, r] using
      (avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n)
  have hMean : (∫ ω, (N ω).toReal ∂P) = r :=
    hNShift.2.trans hMean0
  have hCI : Integrable (fun ω => (N ω).toReal - r) P :=
    hNShift.1.sub (integrable_const r)
  have hCM : (∫ ω, (N ω).toReal - r ∂P) = 0 := by
    rw [integral_sub hNShift.1 (integrable_const r), integral_const, hMean]
    simp [Measure.real]
  have hV :=
    avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
      X s T n
  have hN : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B) := by
    intro ω
    rfl
  exact avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
    X s (s + T) (le_add_of_nonneg_right (zero_le : 0 ≤ T))
    B measurableSet_Iic N hN r hCI hV.1 hCM hV.2
