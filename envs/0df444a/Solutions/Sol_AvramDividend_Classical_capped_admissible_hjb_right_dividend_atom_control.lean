-- Prove2me | solution 1 for AvramDividend.Classical.capped_admissible_hjb_right_dividend_atom_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:42:53.450347+00:00
-- url     : https://prove2.me/submissions/d8414547-c77b-476a-9f6c-71aab9250c7d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
  intro ω t ht
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hd : 0 ≤ rightLimit D t ω - D t ω :=
    (postPaymentReserve_rightJump_decomposition X x D hs ω t).1
  have hpaid :
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω :=
    hD.1.2 ω t ht
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
    by_cases hzero : t = 0
    · subst t
      have hD0 : D 0 ω = 0 := hs.1 ω
      have hX0 : X.X 0 ω = 0 := X.X_zero ω
      simpa only [riskProcess, hX0, hD0, sub_zero, add_zero] using hxc
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm hzero)
      exact hD.2 ω t htpos
  exact local_verification_hjb_controls_dividend_jump_le_cap
    X q w C hw_cont hw_smooth hw_hjb
    (riskProcess X x D t ω)
    (rightLimit D t ω - D t ω) hd hpaid hcap
