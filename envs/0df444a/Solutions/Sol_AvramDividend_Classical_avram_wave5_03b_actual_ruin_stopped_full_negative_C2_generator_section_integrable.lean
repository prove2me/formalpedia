-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:06:44.797402+00:00
-- url     : https://prove2.me/submissions/05ca4486-2619-4fbc-9042-1338afd815e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The stopped original X.generatorIntegrand is a genuine integrable signed
negative-mark source kernel at every actual prepayment reserve; this
is the C² generator form of the nonlinear source Taylor section theorem. -/
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
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      Integrable (fun z : ℝ => JG (p,z))
        (X.ν.restrict (Iio (0 : ℝ))) := by
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
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∀ p : ℝ≥0 × Ω,
    Integrable (fun z : ℝ => JG (p,z))
      (X.ν.restrict (Iio (0 : ℝ)))
  have hInt : ∀ p : ℝ≥0 × Ω,
      Integrable (fun z : ℝ => HS (p,z))
        (X.ν.restrict (Iio (0 : ℝ))) :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
  have hKer (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      HS (p,z) = JG (p,z) := by
    simpa only [HS, H, JG] using
      congrArg (fun r : ℝ =>
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) * r)
        (avram_wave5_03b_actual_source_taylor_generator_kernel_eq
          X x D hD w u v δ p z hz)
  intro p
  have hAE : (fun z : ℝ => HS (p,z)) =ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun z : ℝ => JG (p,z)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with z hz
    exact hKer p z hz
  exact (hInt p).congr hAE
