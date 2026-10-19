-- Prove2me | solution 1 for CarneiroDeSitter.early_time_evolution_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:45:42.378222+00:00
-- url     : https://prove2.me/submissions/63cfb5f0-e11d-4bb3-bafe-e02ce160e1a3

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open CarneiroDeSitter

theorem solution (H ρT ρm pm Λ : ℝ → ℝ) (t : ℝ)
    (hFriedmann : ∀ s, ρT s = 3 * H s ^ 2)
    (hVacuum : ∀ s, Λ s = 3 * H s ^ 4)
    (hSplit : ∀ s, ρT s = ρm s + Λ s)
    (hRadiation : ∀ s, pm s = ρm s / 3)
    (hdiff : DifferentiableAt ℝ H t)
    (hcons : deriv ρT t + 3 * H t * (ρT t + (pm t - Λ t)) = 0)
    (hH : H t ≠ 0) :
    deriv H t + 2 * H t ^ 2 - 2 * H t ^ 4 = 0 := by
  have hρT : ρT = fun s => 3 * H s ^ 2 := funext hFriedmann
  have hd : deriv ρT t = 3 * (2 * H t * deriv H t) := by
    rw [hρT]
    have := (hdiff.hasDerivAt.pow 2).const_mul 3
    refine this.deriv.trans ?_; push_cast; ring
  have hm : ρm t = 3 * H t ^ 2 - 3 * H t ^ 4 := by
    have := hSplit t; rw [hFriedmann, hVacuum] at this; linarith
  rw [hd, hFriedmann, hRadiation, hVacuum, hm] at hcons
  have h6 : 6 * H t * (deriv H t + 2 * H t ^ 2 - 2 * H t ^ 4) = 0 := by linear_combination hcons
  rcases mul_eq_zero.mp h6 with h7 | h7
  · exact absurd (by linarith : H t = 0) hH
  · exact h7
