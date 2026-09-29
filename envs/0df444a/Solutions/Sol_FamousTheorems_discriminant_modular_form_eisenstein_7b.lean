-- Prove2me | solution 1 for FamousTheorems.discriminant_modular_form_eisenstein_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:08:11.145992+00:00
-- url     : https://prove2.me/submissions/28f143f5-e432-48c3-846f-7e52dc7cd8be

import Mathlib

theorem solution (z : UpperHalfPlane) :
    ModularForm.discriminant z = (ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2) / 1728 :=
  ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
