-- Prove2me | solution 1 for Freiman.form_orbit_minimum_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:30.983699+00:00
-- url     : https://prove2.me/submissions/535defe8-801b-4b96-aba9-3afe8b7afa2c

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_orbit_transport_induction
import Theorems.Thm_Freiman_form_step_identity

open Freiman

theorem solution (R : ReducedOrbit) :
    ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n) = reducedMinimum (R.alpha 0) (R.beta 0) := by
  exact form_orbit_transport_induction R (form_step_identity R)
