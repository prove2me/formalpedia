-- Prove2me | solution 1 for DimdPolyLEAN.continuous_ambiguityRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:59.865732+00:00
-- url     : https://prove2.me/submissions/36b26fb6-ae7d-4776-a605-6cb4d8988bfc

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
public import Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_lpPairing
public import Theorems.Thm_DimdPolyLEAN_continuous_modulateL2
public import Theorems.Thm_DimdPolyLEAN_continuous_star_L2

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (f g : L2Real d) :
    Continuous (ambiguityRep f g) := by
  rw [show ambiguityRep f g = fun ξ : PhaseSpace d =>
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2
          (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))) by
    funext ξ
    exact ambiguityRep_eq_lpPairing f g ξ]
  have hfirst : Continuous fun ξ : PhaseSpace d =>
      translateL2 ((1 / 2 : ℝ) • ξ.1) f := (continuous_translateL2_apply f).comp (by fun_prop)
  have htrans : Continuous fun ξ : PhaseSpace d =>
      translateL2 (-((1 / 2 : ℝ) • ξ.1)) g := (continuous_translateL2_apply g).comp (by fun_prop)
  have hstar : Continuous fun ξ : PhaseSpace d =>
      star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g) :=
    continuous_star_L2.comp htrans
  have hsecond : Continuous fun ξ : PhaseSpace d =>
      modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)) :=
    continuous_modulateL2 continuous_snd hstar
  let pairing :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  exact ((pairing.continuous.comp hfirst).clm_apply hsecond)
end DimdPolyLEAN
