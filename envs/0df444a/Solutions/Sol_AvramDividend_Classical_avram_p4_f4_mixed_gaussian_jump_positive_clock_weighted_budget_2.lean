-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f4_mixed_gaussian_jump_positive_clock_weighted_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:29:12.170925+00:00
-- url     : https://prove2.me/submissions/74f591e7-57b3-4632-aa8e-8ff71d3cb01b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_original_uniform_clock_budget_implies_natural_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_positive_clock_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_natural_clock_three_signs
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (hTop : C = ⊤) :
    (∫⁻ ω in {ω | τ ω ≠ 0}, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω | τ ω ≠ 0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hTI, hMean⟩ :=
    avram_p4_f7_original_uniform_clock_budget_implies_natural_L1
      X hX hBV q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI (by
        intro σ F hσstop hσle hFsource hFI k
        have hZ : MeasurableSet {ω : Ω | σ k ω = 0} :=
          avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
            𝓕 (σ k) (hσstop k)
        have hZero : ∀ ω, σ k ω = 0 → F k ω ≤ w x := by
          intro ω hz
          exact avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
            X x q w C D hD hjump (σ k) (F k) (hFsource k) ω hz
        have hPos :=
          (avram_ubv_mixed12_original_positive_clock_expected_upper
            X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
            hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
            n hn τ hτeq hτmeas hτstop W Cash Term
            hW hCash hTerm hTermMeas hCashI σ F
            hσstop hσle hFsource hFI) k
        exact avram_ubv_finite9_turn10_clock_partition_mean_upper
          (w x) (σ k) (F k) hZ (hFI k) hZero hPos)
  let F : Ω → ℝ := fun ω => Term ω + Cash ω
  let σ : ℕ → Ω → ℝ≥0 := fun _ => τ
  have hFI : Integrable F P := hTI.add hCashI
  have hFsource : ∀ k ω, F ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    intro k ω; dsimp [F, σ]
    rw [hTerm ω, hW ω, hCash ω]
  have hPos : (∫ ω in {ω | τ ω ≠ 0}, F ω ∂P) ≤
      w x * (P {ω | τ ω ≠ 0}).toReal := by
    have h := (avram_ubv_mixed12_original_positive_clock_expected_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ (fun _ => F)
      (by intro k; exact hτstop)
      (by intro k ω; exact le_refl _)
      (by intro k ω; exact hFsource k ω)
      (by intro k; exact hFI)) 0
    simpa [σ] using h
  have hB : 0 ≤ w x :=
    (avram_p4_f4_original_natural_clock_three_signs
      X hX hBV q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI).1
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ F ω := Filter.Eventually.of_forall (by
    intro ω
    exact avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
      X x q D τ w C hC hw0 hw_cont hw_neg hw_smooth
      hw_grad W Cash Term hW hCash hTerm hTop ω)
  exact avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
    {ω | τ ω ≠ 0} F (w x) hB hFI hNonneg hPos
