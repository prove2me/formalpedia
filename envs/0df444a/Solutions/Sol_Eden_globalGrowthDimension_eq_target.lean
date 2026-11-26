-- Prove2me | solution 1 for Eden.globalGrowthDimension_eq_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:41.691825+00:00
-- url     : https://prove2.me/submissions/9dc75da4-d188-4889-94f2-55cd8b896f60

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_globalGrowthInterpolation_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c = 4 + 4 / c :=
  (globalGrowthInterpolation_isGreatest hc).csSup_eq
end Eden
