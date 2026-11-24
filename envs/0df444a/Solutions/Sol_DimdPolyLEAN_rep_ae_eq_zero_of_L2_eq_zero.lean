-- Prove2me | solution 1 for DimdPolyLEAN.rep_ae_eq_zero_of_L2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:10.522065+00:00
-- url     : https://prove2.me/submissions/65dd6aa0-ec31-485f-ac58-47564a07fd70

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
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hf_zero : f = 0) :
    fRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
      fun _ => (0 : ℂ) := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  have hcoe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hzero :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun _ => (0 : ℂ) := by
    rw [hf_zero]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 MeasureTheory.volume
  exact hcoe.symm.trans hzero
end DimdPolyLEAN
