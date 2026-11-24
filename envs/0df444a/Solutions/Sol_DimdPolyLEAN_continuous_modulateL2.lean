-- Prove2me | solution 1 for DimdPolyLEAN.continuous_modulateL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:02.198205+00:00
-- url     : https://prove2.me/submissions/843905a2-5c02-4a64-81b6-20f8c257b3fd

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
public import Theorems.Thm_DimdPolyLEAN_continuous_modulateL2_apply
public import Theorems.Thm_DimdPolyLEAN_dist_modulateL2

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} {X : Type*} [TopologicalSpace X]
    {ω : X -> RealVec d} {h : X -> L2Real d}
    (hω : Continuous ω) (hh : Continuous h) :
    Continuous fun x : X => modulateL2 (ω x) (h x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hbase : Tendsto (fun x : X => modulateL2 (ω x) (h x0)) (𝓝 x0)
      (𝓝 (modulateL2 (ω x0) (h x0))) :=
    (continuous_modulateL2_apply (h x0)).continuousAt.comp hω.continuousAt
  refine hbase.congr_dist ?_
  have hdist_h : Tendsto (fun x : X => dist (h x) (h x0)) (𝓝 x0) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hh.continuousAt
  simpa only [dist_modulateL2, dist_comm] using hdist_h
end DimdPolyLEAN
