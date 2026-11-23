-- Prove2me | solution 1 for DensInertW.valuation_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:56.455803+00:00
-- url     : https://prove2.me/submissions/e0357a67-21a8-4340-af09-4ec3ce7565f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Theorems.Thm_DensInertW_val_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution : ValCount := by
  intro K L _ _ _ _ _ h2 n M W hM hW a ha
  first
  | exact val_main h2 hM _ W hW rfl a ha
  | convert val_main h2 hM _ W hW rfl a ha
end DensInertW
