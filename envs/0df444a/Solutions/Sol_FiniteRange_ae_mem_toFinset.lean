-- Prove2me | solution 1 for FiniteRange.ae_mem_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:46.7593+00:00
-- url     : https://prove2.me/submissions/f7521976-f7a6-4f58-9796-f81a52722167

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Theorems.Thm_FiniteRange_null_of_compl

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
namespace FiniteRange
theorem _root_.solution {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    ∀ᵐ x ∂(μ.map X), x ∈ (FiniteRange.toFinset X : Set G) := FiniteRange.null_of_compl μ X hX
end FiniteRange
