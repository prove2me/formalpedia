-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:54:50.853555+00:00
-- url     : https://prove2.me/submissions/13a3e41f-0b9f-46ab-aa59-42d5c602e0b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a58_original_BV_ruinclipped_Ito_Stieltjes_true_source_components
import Theorems.Thm_AvramDividend_Classical_avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- The true stopped Ito-Stieltjes source A58 supplies the genuine source
   components. A57 gives prepayment-strict cash domination without
   replacing D(T) by its right limit or requiring extra L1 assumptions. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∃ (τ : Ω → ℝ≥0),
      (∀ ω, τ ω = (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal) ∧
      (∀ ω, τ ω ≤ S) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      ∃ (W Cash Term M G H : Ω → ℝ),
        (∀ ω, W ω =
          if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω =
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω =
          Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Term P ∧ Integrable Cash P ∧ Integrable M P ∧
        Integrable G P ∧ Integrable H P ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          w x + M ω + G ω + H ω) ∧
        (∀ᵐ ω ∂P, F n ω ≤ Term ω + Cash ω) := by
  classical
  intro δ S F n
  obtain ⟨τ, hτ, hτle, hStop, hRu, W, Cash, Term, M, G, H,
    hW, hCash, hTerm, hTI, hCI, hMI, hGI, hHI,
    hM0, hGH, hLedger, hCashBound, hSurv⟩ :=
    avram_bva_a58_original_BV_ruinclipped_Ito_Stieltjes_true_source_components
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite n
  refine ⟨τ, hτ, hτle, hStop, hRu, W, Cash, Term, M, G, H,
    hW, hCash, hTerm, hTI, hCI, hMI, hGI, hHI,
    hM0, hGH, hLedger, ?_⟩
  exact
    avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite
      n τ W Cash Term hW hTerm hCashBound hSurv
