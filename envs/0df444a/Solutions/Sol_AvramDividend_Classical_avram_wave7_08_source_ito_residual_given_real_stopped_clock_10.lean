-- Prove2me | solution 10 for AvramDividend.Classical.avram_wave7_08_source_ito_residual_given_real_stopped_clock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:28:04.605266+00:00
-- url     : https://prove2.me/submissions/6c5dabab-82a9-4241-92e8-716b1e7534e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_original_natural_terminal_integrable_HJB_mean_upper
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Centre the exact stopped payoff using its expectation and put its
nonpositive mean excess into a finite-variation residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) ∧
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
      AEStronglyMeasurable Term P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
  obtain ⟨hTermI, hMean⟩ :=
    avram_p4_f7_original_natural_terminal_integrable_HJB_mean_upper
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI
  let A : Ω → ℝ := fun ω => Term ω + Cash ω
  let avg : ℝ := ∫ ω, A ω ∂P
  let M : Ω → ℝ := fun ω => A ω - avg
  let G : Ω → ℝ := fun _ => avg - w x
  let H : Ω → ℝ := fun _ => 0
  have hAI : Integrable A P := hTermI.add hCashI
  have hMI : Integrable M P := hAI.sub (integrable_const avg)
  have hGI : Integrable G P := integrable_const _
  have hHI : Integrable H P := integrable_const _
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, A ω - avg ∂P) = 0
    rw [integral_sub hAI (integrable_const avg)]
    simp [avg]
  have hAvg : avg ≤ w x := by simpa [avg, A] using hMean
  have hSign : ∀ᵐ ω ∂P, G ω + H ω ≤ 0 := by
    filter_upwards with ω
    dsimp [G, H]
    linarith
  have hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤
      w x + M ω + G ω + H ω := by
    filter_upwards with ω
    dsimp [M, G, H, A]
    apply le_of_eq
    ring
  exact ⟨W, Cash, Term, M, G, H, hW, hCash, hTerm,
    hTermMeas, hMI, hGI, hHI, hMzero, hSign, hUpper⟩
