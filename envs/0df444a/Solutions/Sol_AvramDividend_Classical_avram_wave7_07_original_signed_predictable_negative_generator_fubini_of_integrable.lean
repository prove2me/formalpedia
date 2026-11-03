-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:15:46.872855+00:00
-- url     : https://prove2.me/submissions/fbd9be71-19dd-405e-bfd3-324f9353b4fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original source stopped compensated Taylor signed-unit Fubini, with
    finite predictable time-clock instance made explicit for the real Bochner
    integral_prod theorem and exact source restricted negative Lévy measure;
    explicit product Bochner integrability as the analytic hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, |a p| ≤ 1) :
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
    (Integrable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
      (S.indicator (fun p => a p.1 * HS p)) r) (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       μ.prod (X.ν.restrict (Iio (0 : ℝ))))) →
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      (S.indicator (fun p => a p.1 * HS p)) r ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       μ.prod (X.ν.restrict (Iio (0 : ℝ))))) = (∫ p : ℝ≥0 × Ω, a p *
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∂μ) := by
  classical
  intro Y H HS hInt
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hFactor :
      (fun r : ((ℝ≥0 × Ω) × ℝ) =>
        (S.indicator (fun p => a p.1 * HS p)) r) =
      (fun r => a r.1 * (S.indicator HS) r) := by
    funext r
    by_cases hr : r ∈ S
    · simp only [Set.indicator_of_mem hr]
    · simp only [Set.indicator_of_notMem hr]
      simp
  rw [hFactor] at hInt ⊢
  calc
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
        a r.1 * (S.indicator HS) r
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
      ∫ p : ℝ≥0 × Ω, ∫ z : ℝ,
        a p * (S.indicator HS) (p,z)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μ := by
        exact MeasureTheory.integral_prod _ hInt
    _ = (∫ p : ℝ≥0 × Ω, a p *
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∂μ) := by
        simp only [integral_const_mul]
