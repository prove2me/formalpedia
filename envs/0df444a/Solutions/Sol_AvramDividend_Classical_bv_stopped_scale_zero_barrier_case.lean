-- Prove2me | solution 1 for AvramDividend.Classical.bv_stopped_scale_zero_barrier_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:26:25.326653+00:00
-- url     : https://prove2.me/submissions/d96e7302-9aa9-49a3-a2be-bac5829c1b38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

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
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hWa : W a = 0) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  obtain ⟨hNeg, hNonneg, hCont, hMono, hLap⟩ := hW
  have hxMem : x ∈ Ici (0 : ℝ) := mem_Ici.mpr hx0
  have haMem : a ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_of_lt ha)
  have hle : W x ≤ W a := hMono hxMem haMem hxa
  rw [hWa] at hle
  have hWxNonneg : 0 ≤ W x := hNonneg x hx0
  have hWx0 : W x = 0 := le_antisymm hle hWxNonneg
  rw [hWa, hWx0, ENNReal.ofReal_zero, mul_zero]
