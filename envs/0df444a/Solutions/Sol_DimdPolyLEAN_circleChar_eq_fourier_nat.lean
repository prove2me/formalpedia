-- Prove2me | solution 1 for DimdPolyLEAN.circleChar_eq_fourier_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:53.784859+00:00
-- url     : https://prove2.me/submissions/eeffe28b-9c50-4cf5-a95d-42472f043b16

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
public import Theorems.Thm_DimdPolyLEAN_circleChar_eq_zeta_pow

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution (n : Nat) (x : Circle) :
    circleChar n x = fourier (n : Int) x := by
  induction n with
  | zero =>
      simp [circleChar]
  | succ n ih =>
      rw [circleChar_eq_zeta_pow, pow_succ]
      change circleChar n x * zeta x = fourier ((n + 1 : Nat) : Int) x
      rw [ih]
      simp only [fourier_apply, Nat.cast_add, Nat.cast_one]
      rw [show ((↑n + 1 : ℤ) • x : AddCircle (2 * Real.pi)) =
          (n : ℤ) • x + x by
        rw [add_zsmul, one_zsmul]]
      rw [AddCircle.toCircle_add]
      rfl
end DimdPolyLEAN
