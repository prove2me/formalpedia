-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_radial_contact_exterior_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T19:52:30.28348+00:00
-- url     : https://prove2.me/submissions/4be0e498-0787-4f5b-a645-d1075a636ad6

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

private theorem radial_contact_differentiable (u w : Phase) :
    DifferentiableAt ℝ (fun x : Phase => phaseRadialContact x w) u ∧
      (∀ v : Phase, fderiv ℝ (fun x : Phase => phaseRadialContact x w) u v =
        phaseRadialContact v w) := by
  let A : Phase →L[ℝ] ℝ := (-1 / 2 : ℝ) •
    (w 2 • ContinuousLinearMap.proj 0 - w 0 • ContinuousLinearMap.proj 2 +
      w 3 • ContinuousLinearMap.proj 1 - w 1 • ContinuousLinearMap.proj 3)
  have heq : (fun x : Phase => phaseRadialContact x w) = A := by
    funext x
    simp [A, phaseRadialContact, phaseSymplecticForm]
    ring
  rw [heq]
  refine ⟨A.differentiableAt, ?_⟩
  intro v
  rw [A.fderiv]
  simp [A, phaseRadialContact, phaseSymplecticForm]
  ring

theorem solution (f : Phase → ℝ)
    (u v w : Phase) (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => f x * phaseRadialContact x v) u w =
    fderiv ℝ f u v * phaseRadialContact u w -
      fderiv ℝ f u w * phaseRadialContact u v - f u * phaseSymplecticForm v w := by
  rw [fderiv_fun_mul hf (radial_contact_differentiable u w).1,
    fderiv_fun_mul hf (radial_contact_differentiable u v).1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [(radial_contact_differentiable u w).2 v, (radial_contact_differentiable u v).2 w]
  simp [phaseRadialContact, phaseSymplecticForm]
  ring
