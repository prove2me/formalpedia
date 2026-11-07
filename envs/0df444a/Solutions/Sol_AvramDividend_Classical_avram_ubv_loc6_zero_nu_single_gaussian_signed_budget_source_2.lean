-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_single_gaussian_signed_budget_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:23:46.663292+00:00
-- url     : https://prove2.me/submissions/ef6c4df3-9ee6-427d-b531-0ea5567ffd07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_gaussian_no_jump_masked_mean_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_masked_sigma_payoff_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Convert the exact physical masked stopped expected budget into five signed
    original-law witnesses, keeping the Ito expectation as its own child. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ Mc G R : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + G ω + R ω) := by
  intro k
  have hσ : X.σ ≠ 0 :=
    avram_p4_f4_original_ubv_zerojump_nonzero_gaussian X hBV hν
  have hHI : Integrable (fun ω => if σ k ω = 0 then w x else F k ω) P :=
    avram_f16_original_masked_sigma_payoff_integrable
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI σ F
      hσstop hσle hFsource hFI k
  have hBound :
      (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x :=
    avram_p4_f11_gaussian_no_jump_masked_mean_budget
      X hX hBV hσ hν q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ
      hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  obtain ⟨Mc, Ms, Ml, G, R, hc, hs, hl, hc0, hs0, hl0,
      hG, hR, hUpper⟩ :=
    avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses
      X (fun ω => if σ k ω = 0 then w x else F k ω) (w x) hHI hBound
  refine ⟨(fun ω => Mc ω + Ms ω + Ml ω),
    (fun ω => G ω + R ω), (fun _ => 0),
    (hc.add hs).add hl, ?_, ?_, ?_, ?_⟩
  · have hsum1 :
        (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
          (∫ ω, Mc ω + Ms ω ∂P) + ∫ ω, Ml ω ∂P := by
      simpa only [Pi.add_apply] using (integral_add (hc.add hs) hl)
    have hsum2 :
        (∫ ω, Mc ω + Ms ω ∂P) =
          (∫ ω, Mc ω ∂P) + ∫ ω, Ms ω ∂P := by
      simpa only [Pi.add_apply] using (integral_add hc hs)
    linarith [hc0, hs0, hl0, hsum1, hsum2]
  · filter_upwards [hG, hR] with ω hg hr
    exact add_nonpos hg hr
  · exact Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ))
  · filter_upwards [hUpper] with ω hh
    linarith
