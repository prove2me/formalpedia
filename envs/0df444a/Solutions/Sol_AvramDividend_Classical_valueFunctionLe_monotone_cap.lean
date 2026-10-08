-- Prove2me | solution 1 for AvramDividend.Classical.valueFunctionLe_monotone_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:56:25.578466+00:00
-- url     : https://prove2.me/submissions/d506ab29-b2e2-4a47-83b9-7f12b38dd6d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (C₁ C₂ : ℝ≥0∞) (hC : C₁ ≤ C₂) :
    valueFunctionLe X q C₁ x ≤ valueFunctionLe X q C₂ x := by
  unfold valueFunctionLe
  refine iSup_le fun D => iSup_le fun hD => ?_
  have hD₂ : IsAdmissibleLe X x C₂ D := by
    refine ⟨hD.1, ?_⟩
    intro ω t ht
    exact (hD.2 ω t ht).trans hC
  exact le_iSup_of_le D (le_iSup_of_le hD₂ le_rfl)
