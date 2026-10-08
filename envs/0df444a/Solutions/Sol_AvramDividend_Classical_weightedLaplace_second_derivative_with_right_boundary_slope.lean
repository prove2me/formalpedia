-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_second_derivative_with_right_boundary_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:52:57.199163+00:00
-- url     : https://prove2.me/submissions/f3f7a833-7e3a-4c48-80d8-04b11ebf6b1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (θ η : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * deriv (deriv W) x) =
      θ ^ 2 * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) - θ * W 0 - η := by
  let V : ℝ → ℝ := fun x => if x = 0 then η else deriv W x
  have hV0 : V 0 = η := by simp [V]
  have hVpos : ∀ x ∈ Ioi (0 : ℝ), V x = deriv W x := by
    intro x hx
    have hxpos : (0 : ℝ) < x := by simpa only [mem_Ioi] using hx
    simp [V, ne_of_gt hxpos]
  have hVnear : V =ᶠ[𝓝[>] (0 : ℝ)] (deriv W) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hVpos x hx
  have hVcont : ContinuousWithinAt V (Ici (0 : ℝ)) 0 := by
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (V 0))
    rw [hV0]
    exact hDlim.congr' hVnear.symm
  have hVderiv :
      ∀ x ∈ Ioi (0 : ℝ),
        HasDerivAt V (deriv (deriv W) x) x := by
    intro x hx
    have heq : V =ᶠ[𝓝 x] (deriv W) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
      exact hVpos z hz
    exact (hderiv1 x hx).congr_of_eventuallyEq heq
  have hVd : ∀ x ∈ Ioi (0 : ℝ),
      deriv V x = deriv (deriv W) x := by
    intro x hx
    exact (hVderiv x hx).deriv
  have hVhas : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt V (deriv V x) x := by
    intro x hx
    exact (hVderiv x hx).congr_deriv (hVd x hx).symm
  have hVint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * V x) (Ioi (0 : ℝ)) := by
    apply hDint.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := volume) measurableSet_Ioi] with x hx
    simp [hVpos x hx]
  have hV2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv V x) (Ioi (0 : ℝ)) := by
    apply hD2int.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := volume) measurableSet_Ioi] with x hx
    simp [hVd x hx]
  have hVibp := weightedLaplace_derivative_with_origin_boundary
    V θ hVcont hVhas hVint hV2int
  have hWibp := weightedLaplace_derivative_with_origin_boundary
    W θ hcont hderiv hWint hDint
  have hD2eq :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv (deriv W) x) =
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv V x) := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := volume) measurableSet_Ioi] with x hx
    rw [hVd x hx]
  have hDeq :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * V x) =
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := volume) measurableSet_Ioi] with x hx
    rw [hVpos x hx]
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * deriv (deriv W) x) =
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv V x) := hD2eq
    _ = θ * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * V x) - V 0 := hVibp
    _ = θ * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) - η := by
          rw [hDeq, hV0]
    _ = θ * (θ * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) - W 0) - η := by
          rw [hWibp]
    _ = θ ^ 2 * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) - θ * W 0 - η := by ring
