-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_positive_clock_finite_grid_signed_budget_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:30:50.487477+00:00
-- url     : https://prove2.me/submissions/bc4caf98-76db-457b-bd20-649258fd8471
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_expected_budget_topcap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_expected_budget_finitecap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_event_expected_budget_supports_centered_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
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
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let A : Set Ω := {ω | σ k ω ≠ 0}
      ∃ (M E : ℕ → Ω → ℝ),
        (∀ j, IntegrableOn (M j) A P) ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, (∫ ω in A, M j ω ∂P) = 0) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F k ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hBudget : ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
    by_cases hTop : C = ⊤
    · exact avram_jump6_B_original_positive_expected_budget_topcap
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI
        hInfiniteActivity hTop
    · exact avram_jump6_B_original_positive_expected_budget_finitecap
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI
        hInfiniteActivity hTop
  intro k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet A := by
    have hZero := avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)
    change MeasurableSet ({ω : Ω | σ k ω = 0}ᶜ)
    exact hZero.compl
  obtain ⟨M, hMI, hMean, hOff, hUpper⟩ :=
    avram_jump6_B_event_expected_budget_supports_centered_ae
      A hA (F k) (hFI k) (w x) (by simpa [A] using hBudget k)
  have hSupported : (A.indicator M) =ᵐ[P] M := by
    filter_upwards [hOff] with ω hω
    by_cases ha : ω ∈ A
    · simp [Set.indicator_of_mem ha]
    · simp [Set.indicator_of_notMem ha, hω ha]
  have hMeanA : (∫ ω in A, M ω ∂P) = 0 := by
    calc
      (∫ ω in A, M ω ∂P) = ∫ ω, A.indicator M ω ∂P :=
        (integral_indicator hA).symm
      _ = ∫ ω, M ω ∂P := integral_congr_ae hSupported
      _ = 0 := hMean
  have hOn : ∀ᵐ ω ∂(P.restrict A), F k ω ≤ w x + M ω := by
    have hIn : ∀ᵐ ω ∂(P.restrict A), ω ∈ A := ae_restrict_mem hA
    filter_upwards [ae_restrict_of_ae hUpper, hIn] with ω hω ha
    exact hω ha
  refine ⟨(fun _ => M), (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hMI.integrableOn
  · intro j
    exact integrableOn_zero
  · intro j
    exact hMeanA
  · intro j
    filter_upwards [hOn] with ω hω
    simpa only [add_zero] using hω
  · simp
