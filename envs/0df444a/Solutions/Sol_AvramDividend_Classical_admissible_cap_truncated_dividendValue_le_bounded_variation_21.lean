-- Prove2me | solution 21 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:22:30.031289+00:00
-- url     : https://prove2.me/submissions/20dd6184-d07b-4345-b840-36dd3048e109
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_survival_terminal_complete_stieltjes_supermartingale
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact BV cash bridge from the stopped survival-terminal supermartingale:
    discard its nonnegative terminal value and transfer real cash to ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hsmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hn
      exact False.elim (hn hBV)
    · intro _
      exact hw_smooth
  obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hsmooth hw_hjb x hxc D hD
  let S : ℝ≥0 := ⟨T, hT⟩
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω))
    else 0
  have hCore : Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x :=
    avram_wave7_04_original_BV_survival_terminal_complete_stieltjes_supermartingale
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hgen hgrad x hx hxc D hD hnonneg hjump T hT
  have hTermNonneg : ∀ ω, 0 ≤ Term ω := by
    intro ω
    dsimp [Term]
    split_ifs <;> simp
  have hMeanNonneg : 0 ≤ ∫ ω, Term ω ∂P :=
    integral_nonneg hTermNonneg
  have hReal :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x :=
    (le_add_of_nonneg_right hMeanNonneg).trans hCore.2
  exact avram_wave7_03_original_full_clock_real_budget_to_ennreal
    X x C D hD T hT q (w x) hReal
