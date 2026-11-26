-- Prove2me | solution 1 for BranchActualQ.nonnegative_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:52:30.594454+00:00
-- url     : https://prove2.me/submissions/4f5ae2ce-04eb-48fd-b112-9d106e98f036

import Theorems.Thm_RHHeight1000_verified_height_bulk
import Theorems.Thm_BranchActualQ_nonnegative_from_verified_height

theorem solution :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u > 0, 0 ≤ Q n u :=
  BranchActualQ.nonnegative_from_verified_height RHHeight1000.verified_height_bulk
#print axioms solution
