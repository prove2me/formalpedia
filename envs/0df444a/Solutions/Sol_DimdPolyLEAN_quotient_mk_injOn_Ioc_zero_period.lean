-- Prove2me | solution 1 for DimdPolyLEAN.quotient_mk_injOn_Ioc_zero_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:03.263666+00:00
-- url     : https://prove2.me/submissions/a6ffaa0c-1e3a-49aa-a087-58c37bb7aea0

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
theorem _root_.solution :
    Set.InjOn (fun t : ℝ => (QuotientAddGroup.mk t : Circle))
      (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hx0 : x ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by simpa only [zero_add, Set.mem_Ioc] using hx
  have hy0 : y ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by simpa only [zero_add, Set.mem_Ioc] using hy
  have hx' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk x : Circle) = ⟨x, hx0⟩ :=
    AddCircle.equivIoc_coe_eq hx0
  have hy' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk y : Circle) = ⟨y, hy0⟩ :=
    AddCircle.equivIoc_coe_eq hy0
  have h := congrArg (AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)) hxy
  rw [hx', hy'] at h
  exact Subtype.ext_iff.mp h
end DimdPolyLEAN
