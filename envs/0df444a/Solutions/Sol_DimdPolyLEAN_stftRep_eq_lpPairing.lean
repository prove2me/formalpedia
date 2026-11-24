-- Prove2me | solution 1 for DimdPolyLEAN.stftRep_eq_lpPairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:45.161714+00:00
-- url     : https://prove2.me/submissions/14845fac-1b74-450b-91ff-d97ac5f9b8f2

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
public import Theorems.Thm_DimdPolyLEAN_translateL2_neg_coeFn
public import Theorems.Thm_DimdPolyLEAN_modulateL2_coeFn

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    stftRep h f ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        f
        (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold stftRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    modulateL2_coeFn ξ.2 (star (translateL2 (-ξ.1) h)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-ξ.1) h),
    translateL2_neg_coeFn ξ.1 h] with t hmod hstar hh
  rw [hmod, hstar]
  simp only [Pi.star_apply]
  rw [hh]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ac_rfl
end DimdPolyLEAN
