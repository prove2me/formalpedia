-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_admissible_BV_physical_HJB_full_budget_source_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:21:40.380969+00:00
-- url     : https://prove2.me/submissions/c538a8c8-8fba-4010-b60d-882aec275da0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_C1_stopped_intrinsic_full_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
/-- Source-exact corrected single signed generator pair: original stopped BV C¹ strong finite-horizon budget from actual maximum HJB, with source-identified physical generator and Stieltjes corrections and intrinsic centred jumps. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (NX : Ω → Measure (ℝ≥0 × ℝ)) (hNX : ∀ ω, NX ω = ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
(MK : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hMK : MK = P.bind K) (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
(hS : MeasurableSet[(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))) (hMT : MT = MK.restrict S)
(μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (hμfinite : μ Set.univ < ∞) (hμclock : ∀ A : Set (ℝ≥0 × Ω),
MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
(hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ))))) (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' → MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C')) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
(hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
(H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)
(hSupport : S.indicator H = H) (Mart : Ω → ℝ) (hMartDef : ∀ ω, Mart ω =
(∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) (q : ℝ) (hq : 0 < q)
(w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
(hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
(X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})) (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
(D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
(hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b, |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : Set (ℝ≥0 × Ω))
(hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
  x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
  Real.exp (-(q * (p.1.1 : ℝ))) *
    (w (Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
     w (Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
(hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) (W Cash Term Gdrift Hdiv : Ω → ℝ)
(hW : ∀ ω, W ω = if (τ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermI : Integrable Term P)
(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P) (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω)) (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) (hGInt : ∀ᵐ ω ∂P, IntegrableOn (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
(B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω)) (hDivRegion : ∀ᵐ ω ∂P, ∀ s, s ∈ B ω → 0 < riskProcess X x D s.toNNReal ω ∧
ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C) (hDivInt : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
(hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω))
 (hIto : ∀ᵐ ω ∂P,
Term ω + Cash ω = w x + Mart ω + Gdrift ω + Hdiv ω) : Integrable Cash P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
(∫ ω, Cash ω ∂P) ≤ w x ∧ (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)  := by
  have hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hc
    rcases hw_hjb y hy hc with ⟨hI, hm⟩
    exact ⟨hI, by rw [← hm]; exact le_max_left _ _⟩
  have hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hc
    have hr := le_max_right (X.generator w y - q * w y) (1 - deriv w y)
    rw [(hw_hjb y hy hc).2] at hr
    linarith
  have hGHnonpos : ∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0 :=
    avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
      X hBV q w C hw_gen hw_grad x D hD T A hAm hRegion hGInt B hBm hDivRegion hDivInt Gdrift Hdiv hGDef hHDef
  exact avram_wave8_22_original_admissible_BV_C1_stopped_intrinsic_full_expected_budget
    X hBV NX hNX K hK MK hMK T S hST hS MT N hMT
    μ hμfinite hμclock hN hFuture τ hτBound hτ
    G H hH hSupport Mart hMartDef q hq
    w C hC hw0 hw_cont hw_neg hw_smooth hw_hjb
    x hx hxc D hD
    a b L R ha ha2 hab hL hR hLip hWbound
    E hEm hEregion hG hτruin
    W Cash Term Gdrift Hdiv hW hCash hTerm hTermI
    hGI hHI hGHnonpos hIto
