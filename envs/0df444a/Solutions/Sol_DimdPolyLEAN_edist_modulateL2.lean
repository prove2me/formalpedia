-- Prove2me | solution 1 for DimdPolyLEAN.edist_modulateL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:29.216857+00:00
-- url     : https://prove2.me/submissions/bdd5f399-c8a5-44c4-bb56-9703cf98983c

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
public import Theorems.Thm_DimdPolyLEAN_modulateL2_coeFn

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    edist (modulateL2 ω f) (modulateL2 ω g) = edist f g := by
  rw [MeasureTheory.Lp.edist_def, MeasureTheory.Lp.edist_def]
  refine MeasureTheory.eLpNorm_congr_norm_ae ?_
  filter_upwards [
    modulateL2_coeFn ω f,
    modulateL2_coeFn ω g] with t hmf hmg
  rw [Pi.sub_apply, Pi.sub_apply, hmf, hmg]
  calc
    ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
        modulationPhase ω t * (g : RealVec d -> ℂ) t‖
        = ‖modulationPhase ω t * ((f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t)‖ := by ring_nf
    _ = ‖(f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t‖ := by
      rw [norm_mul, modulationPhase_norm]
      simp
end DimdPolyLEAN
