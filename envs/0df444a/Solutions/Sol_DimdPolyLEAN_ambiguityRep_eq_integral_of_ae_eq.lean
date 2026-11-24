-- Prove2me | solution 1 for DimdPolyLEAN.ambiguityRep_eq_integral_of_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:45.497529+00:00
-- url     : https://prove2.me/submissions/1caa0ee0-88d0-439b-ac4c-54e82b5347fc

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
    {d : ℕ} {f g : L2Real d} {F G : RealVec d → ℂ}
    (hf : (f : RealVec d → ℂ) =ᵐ[volume] F)
    (hg : (g : RealVec d → ℂ) =ᵐ[volume] G) (ξ : PhaseSpace d) :
    ambiguityRep f g ξ = ∫ t : RealVec d,
      F (t + (1 / 2 : ℝ) • ξ.1) * star (G (t - (1 / 2 : ℝ) • ξ.1)) *
        modulationPhase ξ.2 t := by
  have hplus := ((measurePreserving_add_right volume
    ((1 / 2 : ℝ) • ξ.1)).quasiMeasurePreserving).ae_eq_comp hf
  have hminus : (fun t : RealVec d => (g : RealVec d → ℂ)
      (t - (1 / 2 : ℝ) • ξ.1)) =ᵐ[volume]
      fun t => G (t - (1 / 2 : ℝ) • ξ.1) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      ((measurePreserving_add_right volume
        (-((1 / 2 : ℝ) • ξ.1))).quasiMeasurePreserving).ae_eq_comp hg
  apply integral_congr_ae
  filter_upwards [hplus, hminus] with t htF htG
  exact congrArg (fun a : ℂ => a * modulationPhase ξ.2 t)
    (congrArg₂ (fun a b : ℂ => a * star b) htF htG)
end DimdPolyLEAN
