-- Prove2me | solution 1 for AvramDividend.Classical.avram_a112_original_zero_rate_negative_Borel_physical_count_ae_zero_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:17:10.713428+00:00
-- url     : https://prove2.me/submissions/69a728b0-b58a-4c19-9662-a5ab6626a731

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (hRateZero : X.ν B = 0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    ∀ᵐ ω ∂P, (N ω).toReal = 0 := by
  dsimp
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  have hFirst :
      Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) =
        ((T : ℝ≥0∞) * X.ν B).toReal := by
    simpa only [N] using
      avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg
  have hNonneg : 0 ≤ᵐ[P] (fun ω => (N ω).toReal) :=
    Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
  have hZero : (∫ ω, (N ω).toReal ∂P) = 0 := by
    rw [hFirst.2]
    simp [hRateZero]
  have hAE : (fun ω => (N ω).toReal) =ᵐ[P] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae hNonneg hFirst.1).mp hZero
  change ∀ᵐ ω ∂P, (N ω).toReal = 0
  filter_upwards [hAE] with ω hω
  exact hω
