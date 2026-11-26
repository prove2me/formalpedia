-- Prove2me | solution 1 for Eden.periodicGlobalGrowthIndex_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:15.843637+00:00
-- url     : https://prove2.me/submissions/733833f2-8fc8-4c4d-a5ad-1f2d9dbbfcf5

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthIncrements_eq
import Theorems.Thm_Eden_kaplanYorkeIndex_eq


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 := by
  rw [periodicGlobalGrowthIncrements_eq hc]
  apply kaplanYorkeIndex_eq (by omega)
    (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
  intro k hk hk₅
  interval_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
  linarith
end Eden
