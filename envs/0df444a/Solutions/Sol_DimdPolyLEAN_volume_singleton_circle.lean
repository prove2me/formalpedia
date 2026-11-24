-- Prove2me | solution 1 for DimdPolyLEAN.volume_singleton_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:22.985074+00:00
-- url     : https://prove2.me/submissions/f60e648d-0d8c-494b-8146-91431d2df2af

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
theorem _root_.solution (x : Circle) :
    MeasureTheory.volume ({x} : Set Circle) = 0 := by
  have h := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
  simpa only [Measure.addHaar_singleton, Metric.closedBall_zero, mul_zero, ENNReal.ofReal_min,
    Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat, ENNReal.ofReal_zero, zero_le,
    inf_of_le_right] using h
end DimdPolyLEAN
