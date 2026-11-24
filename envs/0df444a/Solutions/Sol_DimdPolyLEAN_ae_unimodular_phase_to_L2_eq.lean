-- Prove2me | solution 1 for DimdPolyLEAN.ae_unimodular_phase_to_L2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:05.009819+00:00
-- url     : https://prove2.me/submissions/367007cb-bb5c-4007-a7f1-92076b55dc1b

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
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ} {w : ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hphase :
      gRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun u => w * fRep u) :
    g = w • f := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  rcases hg_rep with ⟨hg_mem, hg_eq⟩
  apply MeasureTheory.Lp.ext
  have hg_coe :
      ((g : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] gRep := by
    rw [← hg_eq]
    exact hg_mem.coeFn_toLp
  have hf_coe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hsmul :
      ((w • f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun u => w * fRep u := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul w f, hf_coe] with u hw hf
    rw [hw]
    simp [Pi.smul_apply, smul_eq_mul, hf]
  filter_upwards [hg_coe, hphase, hsmul] with u hg hph hsm
  calc
    ((g : L2Real d) : RealVec d -> ℂ) u = gRep u := hg
    _ = w * fRep u := hph
    _ = ((w • f : L2Real d) : RealVec d -> ℂ) u := hsm.symm
end DimdPolyLEAN
