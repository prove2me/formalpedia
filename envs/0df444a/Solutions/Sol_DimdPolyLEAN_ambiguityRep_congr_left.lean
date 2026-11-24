-- Prove2me | solution 1 for DimdPolyLEAN.ambiguityRep_congr_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:11.661789+00:00
-- url     : https://prove2.me/submissions/52163534-4c1e-4b52-8d97-a783dbe45dd3

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
    {d : Nat} {f f' g : L2Real d} (hf : f = f') :
    ambiguityRep f g = ambiguityRep f' g := by
  subst hf
  rfl
end DimdPolyLEAN
