-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus17_original_shifted_rightcont_conditional_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:42:40.012188+00:00
-- url     : https://prove2.me/submissions/e3c1bb85-7d85-4a82-8dbe-8d46c75bfc64

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus18_original_shifted_centered_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_shifted_physical_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => r)) := by
  dsimp only
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hst : s ≤ s + T :=
    le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le)
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_Ioc
  have hMeanBase :=
    avram_mix_annulus18_original_shifted_centered_first_moment X s T n m hnm
  have hVarBase :=
    avram_mix_annulus16_original_shifted_physical_variance_exact X s T n m hnm
  rcases hMeanBase with ⟨hI, hMean⟩
  rcases hVarBase with ⟨hSq, hVar⟩
  exact avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
    X s (s + T) hst B hB N (by intro ω; rfl)
    r hI hSq hMean hVar
