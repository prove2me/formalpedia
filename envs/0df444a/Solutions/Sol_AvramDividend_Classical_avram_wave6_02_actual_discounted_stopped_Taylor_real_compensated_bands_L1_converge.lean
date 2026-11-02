-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_real_compensated_bands_L1_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:27:41.572335+00:00
-- url     : https://prove2.me/submissions/abd34bcf-5690-4962-be39-c2f23c8a0b81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_intrinsic_source_absolute_error_integral_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let hML : MemLp GW (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
        avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
          X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ;
      ∀ (NX : Ω → Measure (ℝ≥0 × ℝ))
        (hNX : ∀ ω, NX ω =
          ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
            X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
            (fun t : ℝ≥0 => (t, X.X t ω -
              Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
        (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBfinite : ∀ n, (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (B n) < ⊤)
        (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ t, ‖I t‖ = ‖t‖)
        (hZero : ∀ t, ∫ ω, I t ω ∂P = 0)
        (clock : Measure ℝ≥0)
        (hSource : ∀ n,
          (I ((hML.indicator (hB n)).toLp ((B n).indicator GW)) : Ω → ℝ)
            =ᵐ[P] fun ω =>
            (∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
              ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock),
      ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
        Tendsto (fun n => I ((hML.indicator (hB n)).toLp
          ((B n).indicator GW))) Filter.atTop (nhds Llimit) ∧
        Tendsto (fun n =>
          (eLpNorm (fun ω =>
            ((I ((hML.indicator (hB n)).toLp ((B n).indicator GW)) - Llimit) ω : ℝ))
            (1 : ℝ≥0∞) P).toReal) Filter.atTop (nhds 0) ∧
        Tendsto (fun n =>
          ∫ ω, |(I ((hML.indicator (hB n)).toLp ((B n).indicator GW)) -
            Llimit) ω| ∂P) Filter.atTop (nhds 0) ∧
        Tendsto (fun n =>
          ∫ ω, |((∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
            ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock) -
              (Llimit ω : ℝ)| ∂P) Filter.atTop (nhds 0) ∧
        Integrable (fun ω => (Llimit ω : ℝ)) P ∧
        (∫ ω, Llimit ω ∂P) = 0 ∧
        (∀ m n, m ≤ n →
          dist (I ((hML.indicator (hB m)).toLp ((B m).indicator GW)))
            (I ((hML.indicator (hB n)).toLp ((B n).indicator GW))) ≤
            (eLpNorm ((B m)ᶜ.indicator GW) (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) ∧
        (∀ n,
          (I ((hML.indicator (hB n)).toLp ((B n).indicator GW)) : Ω → ℝ)
            =ᵐ[P] fun ω =>
            (∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
              ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock)) := by
  classical
  intro a Y H HS GW
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro hML NX hNX B hB hBfinite hBmono hBcover I hIso hZero clock hSource
  obtain ⟨Llimit, hConv, hL1, hAbs, hInt, hMean, hBand, hSrc⟩ :=
    avram_wave6_02_actual_discounted_stopped_Taylor_intrinsic_source_absolute_error_integral_tendsto_zero
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ
      NX hNX B hB hBfinite hBmono hBcover I hIso hZero clock hSource
  let F : ℕ → Lp ℝ (2 : ℝ≥0∞) P :=
    fun n => I ((hML.indicator (hB n)).toLp ((B n).indicator GW))
  let J : ℕ → Ω → ℝ := fun n ω =>
    (∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
      ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock
  have hAE (n : ℕ) :
      (fun ω => |((F n - Llimit) ω : ℝ)|) =ᵐ[P]
        (fun ω => |J n ω - Llimit ω|) := by
    filter_upwards [Lp.coeFn_sub (F n) Llimit, hSrc n] with ω hsub hsrc
    have hsub' : ((F n - Llimit) ω : ℝ) =
        (F n ω : ℝ) - Llimit ω := by
      simpa only [Pi.sub_apply] using hsub
    have hsrc' : (F n ω : ℝ) = J n ω := hsrc
    exact congrArg abs
      (hsub'.trans (congrArg (fun y : ℝ => y - Llimit ω) hsrc'))
  have hEq (n : ℕ) :
      (∫ ω, |((F n - Llimit) ω : ℝ)| ∂P) =
        (∫ ω, |J n ω - Llimit ω| ∂P) :=
    integral_congr_ae (hAE n)
  have hActual : Tendsto (fun n =>
      ∫ ω, |J n ω - Llimit ω| ∂P) Filter.atTop (nhds 0) := by
    have hFun : (fun n => ∫ ω, |J n ω - Llimit ω| ∂P) =
        (fun n => ∫ ω, |((F n - Llimit) ω : ℝ)| ∂P) := by
      funext n
      exact (hEq n).symm
    rw [hFun]
    exact hAbs
  exact ⟨Llimit, hConv, hL1, hAbs, hActual, hInt, hMean, hBand, hSrc⟩
