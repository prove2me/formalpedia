-- Prove2me | solution 1 for DimdPolyLEAN.continuous_translateL2_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:40.622922+00:00
-- url     : https://prove2.me/submissions/70b4d6e6-37d9-43c0-a7df-a60156fa5588

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
theorem _root_.solution {d : Nat} (f : L2Real d) :
    Continuous fun a : RealVec d => translateL2 a f := by
  have : Fact (Ne (2 : ENNReal) ⊤) := ⟨by norm_num⟩
  unfold translateL2
  refine (DomAddAct.continuous_mk.vadd
    (continuous_const : Continuous fun _ : RealVec d => f)).congr ?_
  intro a
  rfl
end DimdPolyLEAN
