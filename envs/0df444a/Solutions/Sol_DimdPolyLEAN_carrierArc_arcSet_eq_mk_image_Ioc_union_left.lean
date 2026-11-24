-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_arcSet_eq_mk_image_Ioc_union_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:05.469992+00:00
-- url     : https://prove2.me/submissions/b48807b5-239a-4d35-a521-55d1430785df

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Theorems.Thm_DimdPolyLEAN_carrierArc_left_lt_right
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_eq_mk_image_Icc

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      (QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∪
        {(QuotientAddGroup.mk ((carrierArc N k).left) : Circle)} := by
  rw [carrierArc_arcSet_eq_mk_image_Icc k]
  have hIcc :
      Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) ∪
          {((carrierArc N k).left)} := by
    ext y
    constructor
    · intro hy
      by_cases hleft : y = (carrierArc N k).left
      · exact Or.inr hleft
      · exact Or.inl ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft), hy.2⟩
    · intro hy
      rcases hy with hy | hy
      · exact ⟨le_of_lt hy.1, hy.2⟩
      · rw [Set.mem_singleton_iff.mp hy]
        exact ⟨le_rfl, le_of_lt (carrierArc_left_lt_right k)⟩
  rw [hIcc, Set.image_union, Set.image_singleton]
end DimdPolyLEAN
