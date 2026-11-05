-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:25:40.541825+00:00
-- url     : https://prove2.me/submissions/a5c59ad5-dd1a-40ae-8dcf-2884d1a0d125

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    (∫ ω, (N ω).toReal ∂P) = ((T : ℝ≥0∞) * X.ν B).toReal := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  let B : Set ℝ := Iic (-ε)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change (∫ ω, (N ω).toReal ∂P) = ((T : ℝ≥0∞) * X.ν B).toReal
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hBm : MeasurableSet B := measurableSet_Iic
  have hBsep : B ⊆ Iic (-ε) := Subset.rfl
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hBm ε hε hBsep
  have hRate : (∫⁻ ω, N ω ∂P) =
      (((T - 0 : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
    simpa only [tsub_zero] using
      (avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X T B hBm ε hε hBsep)
  have hReal :=
    avram_p2_e_compensator_finite_nu_count_real_mean
      X 0 T (by simp) B hBm hν hRate
  simpa only [tsub_zero] using hReal
