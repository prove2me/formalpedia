-- Prove2me | solution 1 for FiniteRange.null_of_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:06.671406+00:00
-- url     : https://prove2.me/submissions/07c3b548-04fe-4a7c-94f0-a9ab1ddc30e4

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
namespace FiniteRange
theorem _root_.solution {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  rw [Measure.map_apply₀ hX (by measurability)]
  convert measure_empty (μ := μ)
  ext ω
  simp
end FiniteRange
