-- Prove2me | solution 1 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:12:08.962982+00:00
-- url     : https://prove2.me/submissions/7c27d292-83bf-4631-9655-08a35e4139d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  constructor
  · intro x hx hxc
    unfold valueFunctionLe
    refine iSup_le fun D => ?_
    refine iSup_le fun hD => ?_
    exact admissible_cap_dividendValue_le X hX q hq w C hC
      hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD
  · intro htop x hx
    unfold valueFunction
    refine iSup_le fun D => ?_
    refine iSup_le fun hD => ?_
    have hxc : ENNReal.ofReal x ≤ C := by
      rw [htop]
      exact le_top
    have hcap : IsAdmissibleLe X x C D := by
      refine ⟨hD, ?_⟩
      intro ω t ht
      rw [htop]
      exact le_top
    exact admissible_cap_dividendValue_le X hX q hq w C hC
      hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hcap
