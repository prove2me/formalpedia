-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_derivative_with_origin_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:17:30.940134+00:00
-- url     : https://prove2.me/submissions/8bc696e5-abd3-4541-b27d-79da582a0c7d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (θ : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv W x) =
       θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) - W 0 := by
  let F : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * W x
  let F' : ℝ → ℝ := fun x =>
    Real.exp (-(θ * x)) * deriv W x -
      θ * (Real.exp (-(θ * x)) * W x)
  have hFcont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    dsimp [F]
    exact (by fun_prop : ContinuousAt
      (fun x : ℝ => Real.exp (-(θ * x))) 0).continuousWithinAt.mul hcont
  have hFderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    have hl : HasDerivAt (fun t : ℝ => -(θ * t)) (-θ) x := by
      simpa only [id_eq, mul_one, neg_mul] using
        (hasDerivAt_id x).const_mul (-θ)
    have hexp : HasDerivAt
        (fun t : ℝ => Real.exp (-(θ * t)))
        ((-θ) * Real.exp (-(θ * x))) x := by
      simpa only [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-(θ * x))).comp x hl
    have hpoint : F' x =
        ((-θ) * Real.exp (-(θ * x))) * W x +
          Real.exp (-(θ * x)) * deriv W x := by
      dsimp [F']
      ring
    rw [hpoint]
    exact hexp.mul (hderiv x hx)
  have hFint : IntegrableOn F (Ioi (0 : ℝ)) := hWint
  have hF'int : IntegrableOn F' (Ioi (0 : ℝ)) := by
    change IntegrableOn
      (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv W x -
          θ * (Real.exp (-(θ * x)) * W x)) (Ioi (0 : ℝ))
    exact hDint.sub (hWint.const_mul θ)
  have hFlim : Tendsto F atTop (nhds 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hFderiv hF'int hFint
  have hFTC : (∫ x in Ioi (0 : ℝ), F' x) = (0 : ℝ) - F 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hFcont hFderiv hF'int hFlim
  have hintF' :
      (∫ x in Ioi (0 : ℝ), F' x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv W x) -
          θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) := by
    change (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * deriv W x -
        θ * (Real.exp (-(θ * x)) * W x)) = _
    rw [integral_sub hDint (hWint.const_mul θ), integral_const_mul]
  have hFzero : F 0 = W 0 := by simp [F]
  rw [hintF', hFzero] at hFTC
  linarith
