-- Prove2me | solution 4 for AvramDividend.Classical.avram_p4_f4_original_stopped_terminal_integrable_natural_clock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:45:05.707429+00:00
-- url     : https://prove2.me/submissions/2d40a290-636c-40b0-8206-2e913958cee9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_f9_original_compact_terminal_integrable_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
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
    (hCashI : Integrable Cash P) : Integrable Term P  := by
  by_cases hTop : C = ⊤
  · obtain ⟨θ, K, hθ, hK, hwGrowth⟩ :=
      avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hTop
    have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
      intro ω
      rw [hτeq ω]
      have hle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤
          (n : ℝ≥0∞) := min_le_right _ _
      simpa using (ENNReal.toNNReal_mono (by simp) hle)
    have hPos : ∀ᵐ ω ∂P, 0 ≤ Term ω :=
      Filter.Eventually.of_forall
        (avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
          X q w C hTop hw0 hw_cont hw_neg hw_smooth hw_grad
          x D τ W Term hW hTerm)
    exact avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
      X C x D hD τ W Term hτmeas hτstop (n : ℝ≥0) hτbound
      hW w q θ K hθ hK hwGrowth hTerm hTermMeas hPos
  · exact avram_f9_original_compact_terminal_integrable_finite_cap
      X hX hBV q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI hTop
