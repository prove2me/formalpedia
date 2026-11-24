-- Prove2me | solution 1 for DimdPolyLEAN.circleIntegral_split_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:46.81003+00:00
-- url     : https://prove2.me/submissions/707265d5-8062-4c91-a739-c7ba38cfa37d

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

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    (s : Set Circle) (hs : MeasurableSet s) {f : Circle -> ℝ}
    (hf : MeasureTheory.Integrable f μCircle) :
    ∫ x, f x ∂ μCircle =
      ∫ x in s, f x ∂ μCircle + ∫ x in sᶜ, f x ∂ μCircle :=
  (MeasureTheory.integral_add_compl (μ := μCircle) (f := f) hs hf).symm
end DimdPolyLEAN
