-- Prove2me | solution 1 for Eden.periodicGlobalGrowthInterpolation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:58.605709+00:00
-- url     : https://prove2.me/submissions/3e856e0e-2805-4b6a-8f9f-d9c88f68ce08

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthIncrements_eq

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (d : ℝ) :
    periodicGlobalGrowthInterpolation c d = spectrumInterpolation ![2, 0, -2, -2, -c] d := by
  rw [periodicGlobalGrowthInterpolation, periodicGlobalGrowthIncrements_eq hc]
end Eden
