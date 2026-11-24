-- Prove2me | solution 1 for DimdPolyLEAN.continuous_stftRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:59.148746+00:00
-- url     : https://prove2.me/submissions/1b5ff7df-5717-4ced-a479-28c82cc3eef6

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
public import Theorems.Thm_DimdPolyLEAN_continuous_translateL2_apply
public import Theorems.Thm_DimdPolyLEAN_continuous_modulateL2
public import Theorems.Thm_DimdPolyLEAN_continuous_star_L2
public import Theorems.Thm_DimdPolyLEAN_stftRep_eq_lpPairing

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (h f : L2Real d) :
    Continuous (stftRep h f) := by
  rw [show stftRep h f = fun ξ : PhaseSpace d =>
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        f
        (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))) by
    funext ξ
    exact stftRep_eq_lpPairing h f ξ]
  have htrans : Continuous fun ξ : PhaseSpace d =>
      translateL2 (-ξ.1) h := (continuous_translateL2_apply h).comp (by fun_prop)
  have hstar : Continuous fun ξ : PhaseSpace d =>
      star (translateL2 (-ξ.1) h) :=
    continuous_star_L2.comp htrans
  have hsecond : Continuous fun ξ : PhaseSpace d =>
      modulateL2 ξ.2 (star (translateL2 (-ξ.1) h)) := continuous_modulateL2 continuous_snd hstar
  let pairing :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  exact (pairing f).continuous.comp hsecond
end DimdPolyLEAN
