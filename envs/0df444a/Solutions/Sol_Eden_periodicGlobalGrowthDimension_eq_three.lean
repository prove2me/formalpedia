-- Prove2me | solution 1 for Eden.periodicGlobalGrowthDimension_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:58.965552+00:00
-- url     : https://prove2.me/submissions/94b7de59-46aa-4293-ad97-2f7339687ed9

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    periodicGlobalGrowthDimension c = 3 :=
  (periodicGlobalGrowthInterpolation_isGreatest hc).csSup_eq
end Eden
