-- Prove2me | solution 1 for FiniteRange.real_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:31.726424+00:00
-- url     : https://prove2.me/submissions/24e36d98-fb3d-4f58-a29a-6516a2f610d7

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Theorems.Thm_FiniteRange_full

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
namespace FiniteRange
theorem _root_.solution {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X).real (FiniteRange.toFinset X) = μ.real Set.univ := by
  simp [measureReal_def, FiniteRange.full hX]
end FiniteRange
