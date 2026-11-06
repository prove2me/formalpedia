-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:16:12.294548+00:00
-- url     : https://prove2.me/submissions/a4ea28cd-4337-464b-847e-7cea33029c74

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original full negative-cutoff physical marked count has exact centred variance equal to its Lévy mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r
  have hF :=
    avram_p4_f2_original_band_count_factorial_moment_exact X T n
  have hFirst :=
    avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  have hL2 : MemLp (fun ω => (N ω).toReal - r) 2 P := by
    simpa only [tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T n 0 T (show (0 : ℝ≥0) ≤ T from zero_le) le_rfl
          B measurableSet_Iic (Subset.rfl))
  have hCI : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P :=
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2
  have hNI : Integrable (fun ω => (N ω).toReal) P := by
    have h := (hL2.integrable (by norm_num)).add (integrable_const r)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [Pi.add_apply]))
  have hScaleI : Integrable (fun ω => (1 - 2 * r) * (N ω).toReal) P :=
    hNI.const_mul _
  have hScale :
      (∫ ω, (1 - 2 * r) * (N ω).toReal ∂P) =
        (1 - 2 * r) * (∫ ω, (N ω).toReal ∂P) := by
    simp only [integral_const_mul, smul_eq_mul]
  have hConst : (∫ _ : Ω, (r ^ 2 : ℝ) ∂P) = r ^ 2 := by
    simp
  constructor
  · exact hCI
  · calc
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) =
          ∫ ω, ((N ω).toReal * ((N ω).toReal - 1) +
            (1 - 2 * r) * (N ω).toReal) + r ^ 2 ∂P := by
              congr 1
              funext ω
              ring
      _ = (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) +
          (1 - 2 * r) * (∫ ω, (N ω).toReal ∂P) + r ^ 2 := by
            calc
              (∫ ω, ((N ω).toReal * ((N ω).toReal - 1) +
                  (1 - 2 * r) * (N ω).toReal) + r ^ 2 ∂P) =
                  (∫ ω, (N ω).toReal * ((N ω).toReal - 1) +
                    (1 - 2 * r) * (N ω).toReal ∂P) +
                    (∫ _ : Ω, (r ^ 2 : ℝ) ∂P) := by
                      exact integral_add (hF.1.add hScaleI) (integrable_const _)
              _ = _ := by
                rw [integral_add hF.1 hScaleI, hScale, hConst]
      _ = r := by
          rw [hF.2, hFirst]
          ring
