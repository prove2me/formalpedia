-- Prove2me | solution 1 for DimdPolyLEAN.muCircle_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:06.034841+00:00
-- url     : https://prove2.me/submissions/c69c007e-3c67-4790-a198-88e1893d72fe

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
public import Theorems.Thm_DimdPolyLEAN_volume_singleton_circle

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution (x : Circle) :
    μCircle ({x} : Set Circle) = 0 := by
  have hvol : MeasureTheory.volume ({x} : Set Circle) = 0 :=
    volume_singleton_circle x
  rw [AddCircle.volume_eq_smul_haarAddCircle, MeasureTheory.Measure.smul_apply] at hvol
  rw [smul_eq_mul] at hvol
  have hcoef : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by simp [ENNReal.ofReal_eq_zero, Real.pi_pos]
  simpa only [μCircle, Measure.addHaar_singleton] using (mul_eq_zero.mp hvol).resolve_left hcoef
end DimdPolyLEAN
