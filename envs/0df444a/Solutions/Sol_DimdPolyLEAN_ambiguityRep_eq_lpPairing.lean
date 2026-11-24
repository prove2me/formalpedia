-- Prove2me | solution 1 for DimdPolyLEAN.ambiguityRep_eq_lpPairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:46.855324+00:00
-- url     : https://prove2.me/submissions/ef91b349-2ef9-48f0-bef2-ac3d28049f11

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
public import Theorems.Thm_DimdPolyLEAN_translateL2_coeFn
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
    {d : Nat} (f g : L2Real d) (ξ : PhaseSpace d) :
    ambiguityRep f g ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2
          (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold ambiguityRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    translateL2_coeFn ((1 / 2 : ℝ) • ξ.1) f,
    modulateL2_coeFn ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g),
    translateL2_neg_coeFn ((1 / 2 : ℝ) • ξ.1) g] with t hf hmod hstar hg
  rw [hf, hmod, hstar]
  simp only [Pi.star_apply]
  rw [hg]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ac_rfl
end DimdPolyLEAN
