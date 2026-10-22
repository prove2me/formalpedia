-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_contact_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:18.775911+00:00
-- url     : https://prove2.me/submissions/20f84f3c-e194-4000-b16a-2d1c80b4ee2c

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (u w : Phase) :
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
