-- Prove2me | solution 1 for FamousTheorems.hausdorff_dimension_real_pi_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:58:25.627161+00:00
-- url     : https://prove2.me/submissions/fdf66743-65ef-4730-8198-09c136defc87

import Mathlib

theorem solution (n : ℕ) : dimH (Set.univ : Set (Fin n → ℝ)) = n :=
  Real.dimH_univ_pi_fin n
