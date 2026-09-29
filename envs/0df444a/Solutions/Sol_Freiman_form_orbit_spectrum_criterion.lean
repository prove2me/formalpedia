-- Prove2me | solution 1 for Freiman.form_orbit_spectrum_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:41.460304+00:00
-- url     : https://prove2.me/submissions/45e1c75f-9354-4f78-a951-c26abcdf0405

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_positive_reciprocal_infimum_iff
import Theorems.Thm_Freiman_form_orbit_localValue
import Theorems.Thm_Freiman_form_minimum_identity

open Freiman

theorem solution (R : ReducedOrbit) (t : ℝ) :
    ((∀ n : ℤ, localValue R.digits n ≤ t) ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℤ, t-ε<localValue R.digits n) ↔
      0 < reducedMinimum (R.alpha 0) (R.beta 0) ∧ t=1/reducedMinimum (R.alpha 0) (R.beta 0) := by
  have h := positive_reciprocal_infimum_iff (fun n => R.alpha n + R.beta n)
    (fun n => by linarith [R.alpha_gt n, R.beta_pos n]) t
  simp_rw [form_orbit_localValue] at h
  have hi : sInf (Set.range (fun n : ℤ => 1 / localValue R.digits n)) =
      reducedMinimum (R.alpha 0) (R.beta 0) := by
    rw [form_minimum_identity]
    unfold orbitReciprocalInfimum
    simp_rw [form_orbit_localValue]
  rw [hi] at h
  exact h
