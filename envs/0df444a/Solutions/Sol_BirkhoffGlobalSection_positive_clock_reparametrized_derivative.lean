-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_clock_reparametrized_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:07:38.590152+00:00
-- url     : https://prove2.me/submissions/cafb7656-0f11-4026-8e2c-ef44b5d94e52

import Mathlib

open Set
open scoped Topology ContDiff

set_option autoImplicit false

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (clock : ℝ ≃o ℝ) (r : ℝ → ℝ) (y X : ℝ → E)
    (hd : ∀ t, HasDerivAt clock (r t) t) (hpos : ∀ t, 0 < r t)
    (hy : ∀ t, HasDerivAt y (X t) t) (t : ℝ) :
    HasDerivAt (fun v => y (clock.symm v))
      ((r (clock.symm t))⁻¹ • X (clock.symm t)) t := by
  have hc : ContinuousAt clock.symm t := clock.symm.continuous.continuousAt
  have h1 : HasDerivAt clock.symm (r (clock.symm t))⁻¹ t := by
    have := hd (clock.symm t)
    exact HasDerivAt.of_local_left_inverse hc (by simpa using this) (hpos _).ne'
      (Filter.Eventually.of_forall fun s => clock.apply_symm_apply s)
  exact (hy (clock.symm t)).scomp t h1
