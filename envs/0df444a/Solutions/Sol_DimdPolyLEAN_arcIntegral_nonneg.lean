-- Prove2me | solution 1 for DimdPolyLEAN.arcIntegral_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:00.920847+00:00
-- url     : https://prove2.me/submissions/147cc97e-1b3e-4440-a63a-faaf78df8e2d

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
    (I : CircleArc) {f : Circle -> ℝ}
    (hf : ∀ x ∈ arcSet I, 0 <= f x) :
    0 <= arcIntegral I f := by
  unfold arcIntegral
  refine MeasureTheory.integral_nonneg_of_ae ?_
  exact (MeasureTheory.ae_restrict_mem (measurableSet_arcSet I)).mono fun x hx => hf x hx
end DimdPolyLEAN
