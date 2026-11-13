-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:23:02.349483+00:00
-- url     : https://prove2.me/submissions/5b4bea52-bd94-427a-9978-8c1f22759967

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB190_nnreal_time_process_measurable_real_time_swapped
import Theorems.Thm_AvramDividend_Classical_avram_gbB188_joint_measurable_real_occupation_mass
import Theorems.Thm_AvramDividend_Classical_avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = y} = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ → ℝ := fun ω t =>
    x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
  have hYnn : Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) :=
    avram_wave8_20_original_postpayment_reserve_joint_measurable
      X x D hD
  have hYj : Measurable (fun z : Ω × ℝ => Y z.1 z.2) := by
    exact avram_gbB190_nnreal_time_process_measurable_real_time_swapped
      (fun s ω => x + X.X s ω - rightLimit D s ω) hYnn
  have hYsec : ∀ ω, Measurable (Y ω) := by
    intro ω
    exact hYj.comp (measurable_const.prodMk measurable_id)
  have hOcc : Measurable (fun z : Ω × ℝ =>
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2}) :=
    avram_gbB188_joint_measurable_real_occupation_mass Y hYj n
  have hPath : ∀ᵐ ω ∂P, ∀ᵐ y ∂(volume : Measure ℝ),
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = y} = 0 := by
    exact Filter.Eventually.of_forall (fun ω =>
      avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path
        (Y ω) (hYsec ω) n)
  have hSet : MeasurableSet {z : Ω × ℝ |
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2} = 0} := by
    exact hOcc (measurableSet_singleton 0)
  have hFubini := (Measure.ae_ae_comm hSet).mp hPath
  simpa only [Y] using hFubini
