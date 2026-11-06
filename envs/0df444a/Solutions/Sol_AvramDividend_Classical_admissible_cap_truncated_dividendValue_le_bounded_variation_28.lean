-- Prove2me | solution 28 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:55:35.165227+00:00
-- url     : https://prove2.me/submissions/ba27d8de-7be9-4534-ab68-4903bd8e476c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
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
  have hwParts := local_verification_hjb_implies_components X q w C hw_hjb
  have hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    exact ⟨(hwParts y hy hyC).1, (hwParts y hy hyC).2.1⟩
  have hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    exact (hwParts y hy hyC).2.2
  have hwSmoothPair :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun h => (h hBV).elim, fun _ => hw_smooth⟩
  have hwNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t _ hBefore
    have hRange := capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t hBefore
    exact le_trans hRange.1
      (hjb_candidate_ge_capital X q w C hw_cont hw0
        hwSmoothPair hw_hjb (riskProcess X x D t ω) hRange.1 hRange.2)
  have hwJump := avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
    X C hC w hw_cont hw_smooth hwGrad x hxc D hD
  rcases eq_or_lt_of_le hT with hTzero | hTpos
  · subst T
    exact avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hwGen hwGrad x hxc D hD hwNonneg
  · let S : ℝ≥0 := ⟨T, hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0
    have hSM := avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hwGen hwGrad x hx hxc D hD hwNonneg hwJump T hT hTpos
    have hTermNN : ∀ ω, 0 ≤ Term ω := by
      intro ω
      dsimp [Term]
      split_ifs <;> positivity
    exact avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
      X x C D hD q (le_of_lt hq) T hT (w x) Term
      (by simpa only [S, Term] using hSM.1)
      hTermNN
      (by simpa only [S, Term] using hSM.2)
