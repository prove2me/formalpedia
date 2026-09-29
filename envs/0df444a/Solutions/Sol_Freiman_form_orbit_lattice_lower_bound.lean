-- Prove2me | solution 1 for Freiman.form_orbit_lattice_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:41.39928+00:00
-- url     : https://prove2.me/submissions/3d04697d-ff8c-4b2a-a6a4-9e6826d28dfc

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_quadratic_lattice_descent_induction
import Theorems.Thm_Freiman_form_orbit_axis_bound
import Theorems.Thm_Freiman_form_lattice_descent_positive
import Theorems.Thm_Freiman_form_lattice_descent_negative

open Freiman

theorem solution (R : ReducedOrbit) :
    ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  apply quadratic_lattice_descent_induction R (form_orbit_axis_bound R)
  · intro n p q hp hq hv
    exact ⟨n+1, q, p-((R.digits n:ℕ):ℤ)*q, form_lattice_descent_positive R n p q hp hq hv⟩
  · intro n p q hp hq hv
    exact ⟨n-1, ((R.digits (n-1):ℕ):ℤ)*p+q, p, form_lattice_descent_negative R n p q hp hq hv⟩
