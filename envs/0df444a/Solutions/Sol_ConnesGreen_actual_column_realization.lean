-- Prove2me | solution 1 for ConnesGreen.actual_column_realization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T03:49:39.786017+00:00
-- url     : https://prove2.me/submissions/fb74997a-2f2e-4a70-b65b-b2b8c18ba374

import Theorems.Thm_ConnesGreen_columnRealization_iff_membership
import Theorems.Thm_ConnesGreen_actual_column_energy_membership
set_option autoImplicit false

theorem solution (t : ℝ) (ht : 0 < t) : ConnesGreen.ColumnRealization t :=
  (ConnesGreen.columnRealization_iff_membership t ht).mpr
    (ConnesGreen.actual_column_energy_membership t ht)
