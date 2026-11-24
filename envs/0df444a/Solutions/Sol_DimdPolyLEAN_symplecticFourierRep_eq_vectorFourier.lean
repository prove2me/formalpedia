-- Prove2me | solution 1 for DimdPolyLEAN.symplecticFourierRep_eq_vectorFourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:49.797799+00:00
-- url     : https://prove2.me/submissions/827ce420-5455-4256-bb58-0bdaa36378c8

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
theorem _root_.solution {d : Nat}
    (F : PhaseSpace d -> ℂ) (ξ : PhaseSpace d) :
    symplecticFourierRep F ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (symplecticFormLinear (d := d)) F ξ := by
  unfold symplecticFourierRep VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with η
  simp [symplecticFormLinear, Real.fourierChar_apply, Circle.smul_def, sub_eq_add_neg,
    mul_assoc, mul_comm]
end DimdPolyLEAN
