-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f4_turn16_infinitecap_purejump_terminal_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:13:54.276108+00:00
-- url     : https://prove2.me/submissions/30606543-3c9c-413e-a16a-ff0d5aeda0d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_purejump_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
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
    (hCtop : C = ⊤) :
    Integrable Term P := by
  obtain ⟨θ, K, hθ, hK, hGrowth⟩ :=
    avram_p4_f4_turn16_purejump_HJB_global_exponential_growth
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hCtop
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
  have hSmoothCases :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro _
      exact hw_smooth
    · intro hbv
      exact False.elim (hBV hbv)
  have hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω :=
    avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
      X q w C hC hw0 hw_cont hw_neg hSmoothCases hw_grad
      x (le_of_lt hx) hxc D hD τ W Term hW hTerm
  exact (avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
    X C x D hD τ W Term hτmeas hτstop (n : ℝ≥0) hτbound
    hW w q θ K hθ hK hGrowth hTerm hTermMeas hTermNonneg).1
