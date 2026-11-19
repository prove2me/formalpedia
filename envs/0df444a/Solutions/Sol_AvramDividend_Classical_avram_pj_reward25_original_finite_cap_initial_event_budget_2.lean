-- Prove2me | solution 2 for AvramDividend.Classical.avram_pj_reward25_original_finite_cap_initial_event_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:14:17.650352+00:00
-- url     : https://prove2.me/submissions/eb7dd506-4980-4d6e-87cf-b4adbd539241
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward37_original_trueclock_full_compensated_linear_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward28_original_trueclock_finitecap_Taylor_HJB_initial_budget
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward31_original_trueclock_finitecap_Taylor_HJB_initial_event_upper
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) : (∫ ω in A, G ω ∂P) ≤ w x * (P A).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  by_contra h
  have heps : 0 < ((∫ ω in A, G ω ∂P) -
      w x * (P A).toReal) / 2 := by linarith
  obtain ⟨Cb,u,v,δ,η,hu,hδ,hδ1,huv,hη,hη1,hv,hvC,hwCb,
      hLi,hLm,hRes⟩ :=
    avram_pj_reward37_original_trueclock_full_compensated_linear_positive_L1
      X hX hBV hSigmaZero q hq w C hC hCfinite hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq hτmeas hτstop ρ hρstop hρle
      G hGdef hGI A hA _ heps
  let T : ℝ≥0 := (n : ℝ≥0)
  let a : (ℝ≥0 × Ω) → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 *
      (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS := fun (p : ((ℝ≥0 × Ω) × ℝ)) =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let GW := fun (p : ((ℝ≥0 × Ω) × ℝ)) => a p.1 * HS p
  let NX := fun (ω : Ω) =>
    ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
      X.X s ω - Function.leftLim (fun t => X.X t ω) s ≠ 0}).map
      (fun s => (s, X.X s ω - Function.leftLim (fun t => X.X t ω) s)))
  let μT := ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  let J := fun (σ : Ω → ℝ≥0) (ω : Ω) =>
    (∫ p, (if p.1 ≤ σ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
    (∫ t, ∫ z, (if t ≤ σ ω then GW ((t, ω), z) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
  let R : ℝ≥0 × Ω → ℝ := fun p =>
    Real.exp (-(q * (p.1 : ℝ))) *
      ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
        (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
  let B := fun (σ : Ω → ℝ≥0) (ω : Ω) =>
    ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
  let L : Ω → ℝ := fun ω =>
    (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
      Real.exp (-(q * (p.1 : ℝ))) *
        (if Y (p.1, ω) ∈ Icc (u + δ) v then
          deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω)) -
    (∫ t, ∫ z, (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then
      Real.exp (-(q * (t : ℝ))) *
        (if Y (t, ω) ∈ Icc (u + δ) v then
          deriv w (Y (t, ω)) * z else 0) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
  have hJB : Integrable (fun ω => J ρ ω + B ρ ω) P := by
    have h := avram_pj_reward28_original_trueclock_finitecap_Taylor_HJB_initial_budget
      X x D hD.1.1 C hC hCfinite hD w Cb u v δ
      hwCb hw_smooth hw_cont hw_neg hu hδ hδ1 huv hv hvC
      q (le_of_lt hq) hw_gen hw_grad T
    exact (h ρ hρstop).1
  have hJmean : (∫ ω in A, J ρ ω + B ρ ω ∂P) ≤ 0 := by
    have h := avram_pj_reward31_original_trueclock_finitecap_Taylor_HJB_initial_event_upper
      X x D hD.1.1 C hC hCfinite hD w Cb u v δ
      hwCb hw_smooth hw_cont hw_neg hu hδ hδ1 huv hv hvC
      q (le_of_lt hq) hw_gen hw_grad T
    exact h ρ hρstop A hA
  have hLI : Integrable L P := by
    simpa only [T,a,Y,H,HS,GW,NX,μT,J,R,B,L] using hLi
  have hLM : (∫ ω in A, L ω ∂P) = 0 := by
    simpa only [T,a,Y,H,HS,GW,NX,μT,J,R,B,L] using hLm
  have hRem : (∫ ω in A,
      max (0 : ℝ) (G ω - w x - (J ρ ω + B ρ ω + L ω)) ∂P) ≤
      ((∫ ω in A, G ω ∂P) - w x * (P A).toReal) / 2 := by
    simpa only [T,a,Y,H,HS,GW,NX,μT,J,R,B,L] using hRes
  have htransfer :=
    avram_pj_reward35_integrable_positive_residual_event_budget
      A G (fun ω => (J ρ ω + B ρ ω) + L ω) (w x)
      (((∫ ω in A, G ω ∂P) - w x * (P A).toReal) / 2)
      hGI (hJB.add hLI) hRem
  have hsplit : (∫ ω in A, (J ρ ω + B ρ ω) + L ω ∂P) =
      (∫ ω in A, J ρ ω + B ρ ω ∂P) + (∫ ω in A, L ω ∂P) :=
    integral_add hJB.integrableOn hLI.integrableOn
  rw [hsplit,hLM] at htransfer
  linarith
