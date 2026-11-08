-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_fixed_prefix_uniform_L1_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:49:33.201749+00:00
-- url     : https://prove2.me/submissions/218af8b9-963d-4a4f-8409-e6ff7f97776b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_prefix_rightpaid_reserve_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_prefix_clock_reward_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_discount_terminal_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One integrable full-cash majorant controls every fixed-prefix stopped reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hCashI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (B : ℝ) (hB : 0 < x + B)
    (κ : ℕ → Ω → ℝ≥0) (hκle : ∀ j ω, κ j ω ≤ τ ω)
    (hκprefix : ∀ j ω (t : ℝ≥0), t ≤ κ j ω → X.X t ω ≤ B) :
    ∃ g : Ω → ℝ, Integrable g P ∧ ∀ j, ∀ᵐ ω ∂P,
      |Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal| ≤
      g ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let g : Ω → ℝ := fun ω => w (x + B) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hg : Integrable g P := by
    have hc : Integrable (fun _ : Ω => w (x + B)) P := integrable_const _
    simpa [g] using hc.add hCashI
  refine ⟨g, hg, ?_⟩
  intro j
  have hUpper :=
    avram_ubv_top9_original_prefix_clock_reward_L1_envelope
      X w C hTop hw0 hw_cont hw_neg hw_smooth q hq hw_gen hw_grad
      x D hD τ (κ j) (hκle j) T hτBound B hB (hκprefix j)
  let V : Ω → ℝ := fun ω =>
    if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
    else riskProcess X x D (κ j ω) ω
  have hV : ∀ ω, V ω ≤ x + B :=
    avram_ubv_top9_original_prefix_rightpaid_reserve_upper
      X x D hD.1.1 (κ j) B (hκprefix j)
  have hTerm : ∀ ω, 0 ≤
      Real.exp (-(q * (κ j ω : ℝ))) * w (V ω) := by
    intro ω
    exact (avram_ubv_top9_source_topcap_discount_terminal_envelope
      X w C hTop hw0 hw_cont hw_neg hw_smooth q hq hw_gen hw_grad
      (x + B) hB V hV (κ j) ω).1
  filter_upwards [hUpper] with ω hUp
  have hCash : 0 ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal :=
    ENNReal.toReal_nonneg
  have hNonneg : 0 ≤
      Real.exp (-(q * (κ j ω : ℝ))) * w (V ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal :=
    add_nonneg (hTerm ω) hCash
  change |Real.exp (-(q * (κ j ω : ℝ))) * w (V ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal| ≤
      g ω
  rw [abs_of_nonneg hNonneg]
  exact hUp