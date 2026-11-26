-- Prove2me | solution 1 for Eden.periodic_dimension_conventions_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:01.977105+00:00
-- url     : https://prove2.me/submissions/547b11c4-6f77-482f-9630-8aae5eae532f

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_supremum_commonIndexLocalDimension_periodic
import Theorems.Thm_Eden_supremum_asymptoticDimension_periodic


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) := by
  rw [supremum_asymptoticDimension_periodic hc, supremum_commonIndexLocalDimension_periodic hc]
  have : (2 : ℝ) / c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith
end Eden
