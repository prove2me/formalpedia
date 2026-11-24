-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_arcSet_ae_eq_mk_image_Ioc_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:47.515627+00:00
-- url     : https://prove2.me/submissions/bc5cac68-019f-4bfe-91e2-4715f29d8929

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_eq_mk_image_Ioc_union_left
public import Theorems.Thm_DimdPolyLEAN_volume_singleton_circle
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_of_singleton_null
    {N : Nat} (k : Fin N) (μ : MeasureTheory.Measure Circle)
    (hsingleton : ∀ x : Circle, μ ({x} : Set Circle) = 0) :
    arcSet (carrierArc N k) =ᵐ[μ]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[μ] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null (μ := μ) (t := {e}) ?_ (hsingleton e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null (μ := μ) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Circle)]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) :=
  carrierArc_arcSet_ae_eq_mk_image_Ioc_of_singleton_null k _ volume_singleton_circle
end DimdPolyLEAN
