-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_count_variance_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:27:10.521298+00:00
-- url     : https://prove2.me/submissions/04c68edd-dd1a-47bf-a19f-d7bf2c7f8ad6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original marked-annulus Poisson variance from its physical factorial pair moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
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
  have hB : MeasurableSet B := measurableSet_Ioc
  have hSep : B ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hF :=
    avram_mixed_source13_original_physical_annulus_factorial_moment_exact
      X T n m hnm
  have hCtr :
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by
    simpa only [tsub_zero] using
      (avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
        X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) B hB
        (1 / ((m : ℝ) + 1)) (by positivity) hSep).2
  have hL2 : MemLp (fun ω => (N ω).toReal - r) 2 P := by
    simpa only [tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T m 0 T (show (0 : ℝ≥0) ≤ T from zero_le) le_rfl B hB hSep)
  have hCI : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P :=
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2
  have hLinI : Integrable
      (fun ω => (1 - 2 * r) * ((N ω).toReal - r)) P :=
    (hL2.integrable (by norm_num)).const_mul _
  have hScale :
      (∫ ω, (1 - 2 * r) * ((N ω).toReal - r) ∂P) =
        (1 - 2 * r) * (∫ ω, (N ω).toReal - r ∂P) := by
    simp only [integral_const_mul, smul_eq_mul]
  have hConst : (∫ _ : Ω, (r - r ^ 2 : ℝ) ∂P) = r - r ^ 2 := by
    simp
  constructor
  · exact hCI
  · calc
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) =
        ∫ ω, ((N ω).toReal * ((N ω).toReal - 1) +
          (1 - 2 * r) * ((N ω).toReal - r)) + (r - r ^ 2) ∂P := by
            congr 1
            funext ω
            ring
      _ = (∫ ω, (N ω).toReal * ((N ω).toReal - 1) +
            (1 - 2 * r) * ((N ω).toReal - r) ∂P) +
          (∫ _ : Ω, (r - r ^ 2 : ℝ) ∂P) := by
            exact integral_add (hF.1.add hLinI) (integrable_const _)
      _ = (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) +
          (1 - 2 * r) * (∫ ω, (N ω).toReal - r ∂P) + (r - r ^ 2) := by
            rw [integral_add hF.1 hLinI, hScale, hConst]
      _ = r := by
          rw [hF.2, hCtr]
          ring
