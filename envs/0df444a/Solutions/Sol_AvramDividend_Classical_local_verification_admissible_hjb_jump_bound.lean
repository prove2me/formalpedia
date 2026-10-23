-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_admissible_hjb_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:48:38.710915+00:00
-- url     : https://prove2.me/submissions/341dca5e-4481-4968-b745-ee03b2c68a52

import Mathlib
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (huC : ENNReal.ofReal (riskProcess X x D t ω) < C) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))  := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.2.1 ω
  have hD_le : D t ω ≤ rightLimit D t ω := by
    unfold rightLimit
    apply le_ciInf
    intro s
    exact hmono (le_of_lt s.property)
  have hd : 0 ≤ rightLimit D t ω - D t ω := sub_nonneg.mpr hD_le
  have hcap :
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω := hD.2 ω t ht
  exact AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap
    X q w C hw_cont hw_smooth hw_hjb
    (riskProcess X x D t ω) (rightLimit D t ω - D t ω)
    hd hcap (le_of_lt huC)
