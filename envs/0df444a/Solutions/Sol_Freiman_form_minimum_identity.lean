-- Prove2me | solution 1 for Freiman.form_minimum_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:41.233803+00:00
-- url     : https://prove2.me/submissions/ab0ac24e-79cd-4b83-a034-56f1fdd83682

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_minimum_infimum_assembly
import Theorems.Thm_Freiman_form_orbit_minimum_invariant
import Theorems.Thm_Freiman_form_orbit_lattice_lower_bound

open Freiman

theorem solution (R : ReducedOrbit) :
    reducedMinimum (R.alpha 0) (R.beta 0) = orbitReciprocalInfimum R := by
  exact form_minimum_infimum_assembly R (form_orbit_minimum_invariant R) (form_orbit_lattice_lower_bound R)
