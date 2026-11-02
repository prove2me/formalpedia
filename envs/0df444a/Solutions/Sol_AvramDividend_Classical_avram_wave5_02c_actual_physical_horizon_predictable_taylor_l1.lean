-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02c_actual_physical_horizon_predictable_taylor_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:05:09.927573+00:00
-- url     : https://prove2.me/submissions/719d5889-340f-482e-b89d-411cc5a85557

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
         (if Y p.1 ∈ Icc (u + δ) v then
           w (Y p.1 + p.2) - w (Y p.1) else 0) -
         (if -1 < p.2 then
           p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
           else 0)
       let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
         (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
       letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  obtain ⟨μ, hμ, hTime, _⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
      X T
  refine ⟨μ, hμ, hTime, ?_⟩
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  change Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
  obtain ⟨hHSmeas, _, hL1⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  refine ⟨hHSmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hMf : Measurable
      (fun p : ((ℝ≥0 × Ω) × ℝ) => ENNReal.ofReal (‖HS p‖)) :=
    ENNReal.measurable_ofReal.comp hHSmeas.norm
  rw [lintegral_prod _ hMf.aemeasurable]
  simpa only [Real.norm_eq_abs] using hL1
