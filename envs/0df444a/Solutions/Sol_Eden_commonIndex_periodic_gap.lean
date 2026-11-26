-- Prove2me | solution 1 for Eden.commonIndex_periodic_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:46.877196+00:00
-- url     : https://prove2.me/submissions/d5d3cfc0-05b8-485d-b5f3-e92acb81557f

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_supremum_commonIndexLocalDimension_periodic
import Theorems.Thm_Eden_commonIndexDimension_eq_target


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c := by
  rw [supremum_commonIndexLocalDimension_periodic hc, commonIndexDimension_eq_target hc]
  have h₂ : (0 : ℝ) < 2 / c := by positivity
  have h₄ : (0 : ℝ) < 4 / c := by positivity
  linarith
end Eden
