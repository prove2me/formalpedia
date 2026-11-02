-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_predictable_L1_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:02:01.646221+00:00
-- url     : https://prove2.me/submissions/19410a89-b7b0-40cd-aa4f-f966a5fb4c8e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite predictable test measure sees finite full negative-mark
absolute Taylor compensator energy for the genuinely controlled original source.
The jump intensity is the actual Lévy measure X.ν (not a formal Poisson law). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hnonneg : ∀ z : ℝ, 0 ≤ w z) (hmono : Monotone w)
    (hu : 0 < u) (hδ : 0 < δ) (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
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
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) < ⊤ := by
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
  change (∫⁻ p : ℝ≥0 × Ω,
    ∫⁻ z in Iio (0 : ℝ), ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) < ⊤
  obtain ⟨M, hM, hgen⟩ :=
    avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
      X w hnonneg hmono C (u + δ) v (by linarith) huv hv hw
  have hmin_ge (z : ℝ) : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hpoint (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      |HS (p,z)| ≤ M * min 1 (z ^ 2) := by
    have hid :=
      avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ p z hz
    change H (p,z) =
      if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0 at hid
    by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · by_cases hb : Y p ∈ Icc (u + δ) v
      · simpa [HS, hs, hid, hb, Real.norm_eq_abs] using hgen (Y p) hb z hz
      · simpa [HS, hs, hid, hb] using mul_nonneg hM (hmin_ge z)
    · simpa [HS, hs] using mul_nonneg hM (hmin_ge z)
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  let S : ℝ≥0∞ := ∫⁻ z in Iio (0 : ℝ), f z ∂X.ν
  have hfmeas : Measurable f := by fun_prop
  have hminmeas : AEStronglyMeasurable
      (fun z : ℝ => min 1 (z ^ 2)) X.ν := by fun_prop
  have hminnonneg : 0 ≤ᵐ[X.ν] (fun z : ℝ => min 1 (z ^ 2)) := by
    filter_upwards with z
    positivity
  have hminfull : Integrable (fun z : ℝ => min 1 (z ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable hminmeas hminnonneg).mp
      (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun z : ℝ => min 1 (z ^ 2))
      (X.ν.restrict (Iio (0 : ℝ))) :=
    hminfull.mono_measure Measure.restrict_le_self
  have hminsection : AEStronglyMeasurable
      (fun z : ℝ => min 1 (z ^ 2))
      (X.ν.restrict (Iio (0 : ℝ))) := by fun_prop
  have hminsection_nonneg :
      0 ≤ᵐ[(X.ν.restrict (Iio (0 : ℝ)))]
        (fun z : ℝ => min 1 (z ^ 2)) := by
    filter_upwards with z
    exact hmin_ge z
  have hSfin : S < ⊤ := by
    have hSne : S ≠ ⊤ :=
      (lintegral_ofReal_ne_top_iff_integrable
        hminsection hminsection_nonneg).mpr hmin
    exact lt_top_iff_ne_top.mpr hSne
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤ ENNReal.ofReal M * S := by
    calc
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal M * f z ∂X.ν := by
          apply setLIntegral_mono (by fun_prop)
          intro z hz
          rw [← ENNReal.ofReal_mul hM]
          exact ENNReal.ofReal_le_ofReal (hpoint p z hz)
      _ = _ := lintegral_const_mul _ hfmeas
  calc
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ), ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) ≤
        ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal M * S ∂μ :=
      lintegral_mono hinner
    _ = μ Set.univ * (ENNReal.ofReal M * S) := by
      simp [mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hμ
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin)
