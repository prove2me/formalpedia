-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/41a38e79-734f-4600-9dd1-43aa4218ec7c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452
namespace Ehrhart.HolomorphicLaurentFourierCompletenessBridge
theorem _root_.solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiod : Function.Periodic f logarithmicPeriod)
    (a b : ℝ) :
    (∫ t : ℝ in 0..2 * Real.pi,
      f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ in 0..2 * Real.pi,
        f ((a : ℂ) + (t : ℂ) * Complex.I) := by
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (⟨a, 0⟩ : ℂ) (⟨b, 2 * Real.pi⟩ : ℂ)
      hf.differentiableOn
  have htop :
      (∫ x : ℝ in a..b,
        f ((x : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in a..b, f (x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simpa [logarithmicPeriod] using hperiod (x : ℂ)
  have heq :
      Complex.I *
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((b : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.I *
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    have hsimpl :
        ((∫ x : ℝ in a..b, f (x : ℂ)) -
          (∫ x : ℝ in a..b,
            f ((x : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) +
          Complex.I *
            (∫ t : ℝ in 0..2 * Real.pi,
              f ((b : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I *
            (∫ t : ℝ in 0..2 * Real.pi,
              f ((a : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
      simpa [smul_eq_mul] using hrect
    rw [htop] at hsimpl
    exact sub_eq_zero.mp (by simpa using hsimpl)
  exact mul_left_cancel₀ Complex.I_ne_zero heq
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
