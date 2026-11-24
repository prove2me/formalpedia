-- Prove2me | solution 1 for DimdPolyLEAN.norm_ambiguityRep_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:27.255896+00:00
-- url     : https://prove2.me/submissions/aaac1a44-9995-482a-a1bb-2acd25186287

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
public import Theorems.Thm_DimdPolyLEAN_norm_translateL2
public import Theorems.Thm_DimdPolyLEAN_norm_modulateL2
public import Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_lpPairing
public import Theorems.Thm_DimdPolyLEAN_norm_star_L2
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem lpPairing_mul_norm_le {d : Nat} (f g : L2Real d) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2) f g‖ ≤ ‖f‖ * ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hleft : B.lpPairing (volume : Measure (RealVec d)) 2 2 f g =
      MeasureTheory.L1.integral (B.holder 1 f g) := by
    rw [MeasureTheory.L1.integral_eq' ℂ]
    rfl
  rw [hleft]
  calc
    _ ≤ ‖B.holder 1 f g‖ := MeasureTheory.L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖g‖ := ContinuousLinearMap.norm_holder_apply_apply_le B f g
    _ ≤ 1 * ‖f‖ * ‖g‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) (norm_nonneg f))
        (norm_nonneg g)
    _ = ‖f‖ * ‖g‖ := by rw [one_mul]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} (f g : L2Real d) (ξ : PhaseSpace d) :
    ‖ambiguityRep f g ξ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ambiguityRep_eq_lpPairing]
  have hpair := lpPairing_mul_norm_le
    (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
    (modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)))
  calc
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)))‖
        ≤ ‖translateL2 ((1 / 2 : ℝ) • ξ.1) f‖ *
            ‖modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))‖ := hpair
    _ = ‖f‖ * ‖g‖ := by rw [norm_translateL2, norm_modulateL2, norm_star_L2, norm_translateL2]
end DimdPolyLEAN
