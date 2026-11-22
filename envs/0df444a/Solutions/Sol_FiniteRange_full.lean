-- Prove2me | solution 1 for FiniteRange.full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:58.114632+00:00
-- url     : https://prove2.me/submissions/266183cc-fb39-45e9-bfac-3d8b0e4a1894

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
namespace FiniteRange
theorem _root_.solution {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by
  rw [Measure.map_apply hX (by measurability)]
  congr
  ext ω
  simp
end FiniteRange
