-- Prove2me | solution 1 for DimdPolyLEAN.edist_star_L2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:52.013462+00:00
-- url     : https://prove2.me/submissions/dac3bf76-ac03-4440-bf71-5027536555c1

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
theorem _root_.solution {d : Nat} (f g : L2Real d) :
    edist (star f) (star g) = edist f g := by
  rw [MeasureTheory.Lp.edist_def, MeasureTheory.Lp.edist_def]
  refine MeasureTheory.eLpNorm_congr_norm_ae ?_
  filter_upwards [
    MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g] with t hf hg
  rw [Pi.sub_apply, Pi.sub_apply, hf, hg]
  simp only [Pi.star_apply]
  calc
    ‖star ((f : RealVec d -> ℂ) t) - star ((g : RealVec d -> ℂ) t)‖
        = ‖star ((f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t)‖ := by rw [star_sub]
    _ = ‖(f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t‖ := norm_star _
end DimdPolyLEAN
