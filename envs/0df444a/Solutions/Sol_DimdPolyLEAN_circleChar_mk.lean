-- Prove2me | solution 1 for DimdPolyLEAN.circleChar_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:35.834424+00:00
-- url     : https://prove2.me/submissions/892e85ca-dfc7-4992-aaf2-ee4e293bb57b

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
theorem _root_.solution (n : Nat) (theta : ℝ) :
    circleChar n (QuotientAddGroup.mk theta : Circle) =
      Complex.exp (Complex.I * (n : ℂ) * theta) := by
  simp only [circleChar, zeta, AddCircle.toCircle, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
    Real.pi_ne_zero, or_self, not_false_eq_true, div_self, one_mul, Function.Periodic.lift_coe,
    Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  ac_rfl
end DimdPolyLEAN
