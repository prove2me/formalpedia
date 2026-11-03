-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_intrinsic_BV_C1_stopped_jump_to_full_HJB_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:59:44.25608+00:00
-- url     : https://prove2.me/submissions/095a5f95-739d-4740-8ef1-5f9f55abc881

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_actual_BV_C1_intrinsic_stopped_compensated_negative_jump_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_source_hjb_expected_budget_conditional_ito
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original signed negative-jump compensation supplies the centred stochastic term in the finite-horizon HJB budget. -/
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
(D : ℝ≥0 → Ω → ℝ) (hDs : IsDividendStrategy 𝓕 D) (hD : IsAdmissibleLe X x C D) (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
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
(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P) (hGHnonpos : ∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0) (hIto : ∀ᵐ ω ∂P,
Term ω + Cash ω = w x + Mart ω + Gdrift ω + Hdiv ω) : Integrable Cash P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
(∫ ω, Cash ω ∂P) ≤ w x ∧ (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  obtain ⟨hCentI, hCentZero⟩ :=
    avram_wave8_22_actual_BV_C1_intrinsic_stopped_compensated_negative_jump_L1_zero_mean
      X hBV NX hNX K hK MK hMK T S hST hS MT N hMT
      μ hμfinite hμclock hN hFuture τ hτBound hτ
      x D hDs w hw_cont hw_neg q (le_of_lt hq)
      a b L R ha ha2 hab hL hR hLip hWbound
      E hEm hEregion G hG H hH hSupport
  have hMartEq : Mart = (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))) :=
    funext hMartDef
  have hMI : Integrable Mart P := by
    rw [hMartEq]
    exact hCentI
  have hMzero : (∫ ω, Mart ω ∂P) = 0 := by
    rw [hMartEq]
    exact hCentZero
  exact avram_wave6_06_original_source_hjb_expected_budget_conditional_ito
    X q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_hjb
    x hx hxc D hD τ T hτBound hτ hτruin
    W Cash Term Mart Gdrift Hdiv hW hCash hTerm hTermI
    hMI hGI hHI hMzero hGHnonpos hIto