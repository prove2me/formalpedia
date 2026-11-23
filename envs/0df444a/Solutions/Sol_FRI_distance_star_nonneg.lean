-- Prove2me | solution 1 for FRI_distance_star_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:26:51.97356+00:00
-- url     : https://prove2.me/submissions/a556b520-76e2-49f3-809f-668f107a96a3

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_relDistanceToSet_nonneg

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (h_bound_valid : bound + 1 / P.D_0.card ≤ 1) :
    0 ≤ FRI_distance_star P f_0 bound := by
  simp only [FRI_distance_star]
  exact le_min (relDistanceToSet_nonneg f_0 (FRI_code P 0).carrier) (by grind)
