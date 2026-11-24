-- Prove2me | solution 1 for DimdPolyLEAN.circleIntegral_union_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:43.934122+00:00
-- url     : https://prove2.me/submissions/186347fd-fd6e-4a6e-ade4-0c50a7695e60

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
public import Theorems.Thm_DimdPolyLEAN_measurableSet_arcSet

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {ι : Type} [Fintype ι] (I : ι -> CircleArc)
    (hdisj : Pairwise fun i j => Disjoint (arcSet (I i)) (arcSet (I j)))
    {f : Circle -> ℝ}
    (hf : ∀ i, MeasureTheory.IntegrableOn f (arcSet (I i)) μCircle) :
    ∫ x in (⋃ i, arcSet (I i)), f x ∂ μCircle =
      ∑ i, arcIntegral (I i) f := by
  simpa only [arcIntegral] using
    (MeasureTheory.integral_iUnion_fintype
      (μ := μCircle) (f := f) (s := fun i => arcSet (I i))
      (fun i => measurableSet_arcSet (I i)) hdisj hf)
end DimdPolyLEAN
