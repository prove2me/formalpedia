-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_simultaneous_source_dividend_jump_without_hjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:25:42.322677+00:00
-- url     : https://prove2.me/submissions/4fce8a5e-de64-41cd-a416-177786369a63

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- In the actual BV controlled reserve the simultaneous source/drop HJB jump is nonpositive without an independent hjump axiom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hMark : X.X t ω ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    (hb : 0 ≤ x +
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal (x +
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
        D t ω) ≤ C) :
    (rightLimit D t ω - D t ω) +
      w (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω)) -
      w (x + Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ 0 := by
  have hJump :=
    avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
      X hX hBV C hC w hw_cont hw_smooth hw_grad
      x hx hxc D hD
  exact
    avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
      X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      x D hD hJump ω t ht hMark hb hbC
