-- Prove2me | solution 1 for Eden.periodicGlobalLogGrowth_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:16.300053+00:00
-- url     : https://prove2.me/submissions/f589c76e-0792-4d5b-8b5e-fd8cad0877b8

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_periodicIntegerGrowthValues_isGreatest

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 ≤ t)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalLogGrowth c k t = t * spectrumPartialSum ![2, 0, -2, -2, -c] k := by
  rw [periodicGlobalLogGrowth, (periodicIntegerGrowthValues_isGreatest hc ht hk).csSup_eq,
    Real.log_exp]
end Eden
