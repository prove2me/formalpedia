-- Prove2me | solution 1 for DimdPolyLEAN.fourier_translate_realVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:01.680113+00:00
-- url     : https://prove2.me/submissions/51404c91-3d10-4fc6-9bd5-e538448f98ca

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
theorem _root_.solution {d : Nat} (a : RealVec d) (f : RealVec d -> ℂ)
    (_hf : Integrable f (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    FourierTransform.fourier (fun t : RealVec d => f (t - a)) =
      fun ω : RealVec d => modulationPhase a ω * FourierTransform.fourier f ω := by
  have h := (VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (L := innerₗ (RealVec d)) (f := f) (v₀ := -a))
  rw [FourierTransform.fourier]
  ext ω
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d))
      (fun t : RealVec d => f (t - a)) ω =
    modulationPhase a ω *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d)) f ω
  have hω := congrFun h ω
  simp only [Function.comp_def] at hω
  simpa only [sub_eq_add_neg, modulationPhase, mul_comm, mul_neg, neg_mul, mul_assoc, map_neg,
    LinearMap.neg_apply, innerₗ_apply_apply, Circle.smul_def, Real.fourierChar_apply,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, mul_left_comm] using
      hω
end DimdPolyLEAN
