-- Prove2me | solution 1 for CarneiroDeSitter.early_time_density_parameters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:45:56.824415+00:00
-- url     : https://prove2.me/submissions/1c574b4a-a1ad-42e6-abb3-eae1e27d38b4

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open CarneiroDeSitter

theorem solution (H ρT ρm Λ : ℝ → ℝ) (t : ℝ)
    (hFriedmann : ∀ s, ρT s = 3 * H s ^ 2)
    (hVacuum : ∀ s, Λ s = 3 * H s ^ 4)
    (hSplit : ∀ s, ρT s = ρm s + Λ s)
    (hode : HasDerivAt H (-2 * H t ^ 2 + 2 * H t ^ 4) t)
    (hH : H t ≠ 0) :
    ρm t / ρT t = 1 - H t ^ 2 ∧ Λ t / ρT t = H t ^ 2 ∧
    decelerationParameter H t = 1 - 2 * H t ^ 2 := by
  have hm : ρm t = 3 * H t ^ 2 - 3 * H t ^ 4 := by
    have := hSplit t; rw [hFriedmann, hVacuum] at this; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, hFriedmann]; field_simp
  · rw [hVacuum, hFriedmann]; field_simp
  · unfold decelerationParameter
    rw [hode.deriv]; field_simp; ring
