-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward42_original_finiteband_initial_event_marked_Campbell_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:02:18.340715+00:00
-- url     : https://prove2.me/submissions/4ba3fd6f-d712-4ba8-924e-9b1466d8926f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward60_original_compact_smallmark_all_stops_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward41_original_finiteband_linear_mark_source_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_compensated_clock_centering
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband) (hvC : v < C.toReal)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
      (let T : ℝ≥0 := (n : ℝ≥0)
      let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      let μT : Measure ℝ≥0 := ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
      let Lsource : Ω → ℝ := fun ω => (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then Real.exp (-(q * (p.1 : ℝ))) * (if Y (p.1, ω) ∈ Icc (u + δ) v then deriv
        w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω))
      let Lclock : Ω → ℝ := fun ω => (∫ t, ∫ z, (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then Real.exp (-(q * (t : ℝ))) * (if Y (t, ω) ∈ Icc (u + δ) v then deriv w
        (Y (t, ω)) * z else 0) else 0) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      (∫ ω in A, Lsource ω ∂P) = (∫ ω in A, Lclock ω ∂P)) := by
  classical
  let T : ℝ≥0 := (n : ℝ≥0)
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
      Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
  let μT : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  let H : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
    if p.1 ≤ T ∧ p.2 ∈ Z then
      Real.exp (-(q * (p.1 : ℝ))) *
        (if Y (p.1, ω) ∈ Icc (u + δ) v then
          deriv w (Y (p.1, ω)) * p.2 else 0) else 0
  let Lsource : Ω → ℝ := fun ω =>
    (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Z then
      Real.exp (-(q * (p.1 : ℝ))) *
      (if Y (p.1, ω) ∈ Icc (u + δ) v then
        deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω))
  let Lclock : Ω → ℝ := fun ω =>
    (∫ t, ∫ z, (if t ≤ ρ ω ∧ z ∈ Z then
      Real.exp (-(q * (t : ℝ))) *
      (if Y (t, ω) ∈ Icc (u + δ) v then
        deriv w (Y (t, ω)) * z else 0) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
  have hρT : ∀ ω, ρ ω ≤ T := by
    intro ω
    exact (hρle ω).trans
      (avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
        X x D n τ hτeq ω)
  have hm (ω : Ω) (p : ℝ≥0 × ℝ) :
      (if p.1 ≤ ρ ω then H ω p else 0) =
      (if p.1 ≤ ρ ω ∧ p.2 ∈ Z then
        Real.exp (-(q * (p.1 : ℝ))) *
        (if Y (p.1, ω) ∈ Icc (u + δ) v then
          deriv w (Y (p.1, ω)) * p.2 else 0) else 0) := by
    by_cases ht : p.1 ≤ ρ ω
    · have hbound : p.1 ≤ T := ht.trans (hρT ω)
      by_cases hz : p.2 ∈ Z <;> simp [H, ht, hz, hbound]
    · simp [H, ht]
  have hUniv :=
    avram_pj_reward60_original_compact_smallmark_all_stops_zero_mean
      X hX hBV hSigmaZero q hq w C hC hCfinite hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq hτmeas hτstop ρ hρstop hρle
      G hGdef hGI A hA Cband u v δ η
      hu hδ hδ1 huv hη hη1 hv hvC hwCb
  have hCen :=
    avram_ubv_jump12_original_initial_event_compensated_clock_centering
      X T A hA ρ hρstop H hUniv
  change (∫ ω in A,
    ((∫ p, (if p.1 ≤ ρ ω then H ω p else 0) ∂(NX ω)) -
     (∫ t, ∫ z, (if t ≤ ρ ω then H ω (t,z) else 0)
       ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) ∂P) = 0 at hCen
  have hCen' : (∫ ω in A, Lsource ω - Lclock ω ∂P) = 0 := by
    convert hCen using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [Lsource, Lclock]
    congr 1
    · apply integral_congr_ae
      filter_upwards [] with p
      exact (hm ω p).symm
    · apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with z
      exact (hm ω (t, z)).symm

  have hI : Integrable Lsource P ∧ Integrable Lclock P := by
    exact avram_pj_reward41_original_finiteband_linear_mark_source_clock_L1
      X hX hBV hSigmaZero q hq w C hC hCfinite hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq hτmeas hτstop ρ hρstop hρle
      G hGdef hGI A hA Cband u v δ η
      hu hδ hδ1 huv hη hη1 hv hvC hwCb
  have heq := hCen'
  rw [integral_sub (hI.1.integrableOn) (hI.2.integrableOn)] at heq
  exact sub_eq_zero.mp heq
