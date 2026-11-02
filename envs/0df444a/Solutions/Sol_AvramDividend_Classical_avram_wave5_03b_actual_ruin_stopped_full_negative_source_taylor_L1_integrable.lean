-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_L1_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:50:02.476205+00:00
-- url     : https://prove2.me/submissions/10569ca3-de99-4a1a-aed0-53b6f92debee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the actual Lévy process X, adapted control D, stopped prepayment
reserve and original negative Lévy intensity X.ν, every fixed-time full-mark
nonlinear Taylor correction has a finite absolute source compensator integral.
The monotonicity/nonnegativity assumptions supply the uniform large-jump bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hnonneg : ∀ z : ℝ, 0 ≤ w z) (hmono : Monotone w)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
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
    ∀ p : ℝ≥0 × Ω,
      Integrable (fun z : ℝ => HS (p,z)) (X.ν.restrict (Iio (0 : ℝ))) := by
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
  change ∀ p : ℝ≥0 × Ω,
    Integrable (fun z : ℝ => HS (p,z)) (X.ν.restrict (Iio (0 : ℝ)))
  obtain ⟨M, hM, hgen⟩ :=
    avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
      X w hnonneg hmono C (u + δ) v
      (by linarith) huv hv hw
  let μ0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable) := 0
  have hμ0 : μ0 Set.univ < ⊤ := by simp [μ0]
  have hpred : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS :=
    (avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2
      X x D hD w 0 C u v δ hw hw_cont hw_neg
      hu (by linarith) hv (le_of_lt hu)
      hδ hδone (le_of_lt huv) μ0 hμ0).1
  have hmin_meas :
      AEStronglyMeasurable (fun z : ℝ => min 1 (z ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun z : ℝ => min 1 (z ^ 2)) := by
    filter_upwards with z
    positivity
  have hmin_full :
      Integrable (fun z : ℝ => min 1 (z ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
       hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun z : ℝ => min 1 (z ^ 2))
      (X.ν.restrict (Iio (0:ℝ))) :=
    hmin_full.mono_measure Measure.restrict_le_self
  have hcontrol :
      Integrable (fun z : ℝ => M * min 1 (z ^ 2))
        (X.ν.restrict (Iio (0 : ℝ))) :=
    hmin.const_mul M
  have hmin_ge (z : ℝ) : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hpoint (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      ‖HS (p,z)‖ ≤ M * min 1 (z ^ 2) := by
    have hid :=
      avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ p z hz
    change H (p,z) =
      if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0 at hid
    by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · by_cases hb : Y p ∈ Icc (u + δ) v
      · simpa [HS, hs, hid, hb] using hgen (Y p) hb z hz
      · simpa [HS, hs, hid, hb] using mul_nonneg hM (hmin_ge z)
    · simpa [HS, hs] using mul_nonneg hM (hmin_ge z)
  intro p
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hpair : Measurable (fun z : ℝ => (p,z)) := by fun_prop
  have hsection : AEStronglyMeasurable
      (fun z : ℝ => HS (p,z)) (X.ν.restrict (Iio (0 : ℝ))) :=
    (hpred.comp hpair).aestronglyMeasurable
  have hnorm : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖HS (p,z)‖ ≤ M * min 1 (z ^ 2) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with z hz
    exact hpoint p z hz
  exact hcontrol.mono' hsection hnorm
