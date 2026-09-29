-- Prove2me | solution 1 for Freiman.form_orbit_localValue
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:41.419636+00:00
-- url     : https://prove2.me/submissions/3a64f09c-d5fd-40c7-81ef-74141375301f

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_orbit_forward_tail
import Theorems.Thm_Freiman_form_orbit_backward_tail

open Freiman

theorem solution (R : ReducedOrbit) (n : ℤ) :
    R.alpha n + R.beta n = localValue R.digits n := by
  rw [form_orbit_forward_tail, form_orbit_backward_tail]
  unfold localValue
  ring
