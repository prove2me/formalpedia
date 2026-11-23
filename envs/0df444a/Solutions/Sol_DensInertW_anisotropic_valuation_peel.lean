-- Prove2me | solution 1 for DensInertW.anisotropic_valuation_peel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:22.239602+00:00
-- url     : https://prove2.me/submissions/61f948a1-c482-4467-a4c2-9de27ec0310f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
import Theorems.Thm_DensInertW_anisoPeel_of_valCount
import Theorems.Thm_DensInertW_valuation_count


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
open DensInertW.Sub
namespace DensInertW
theorem _root_.solution : AnisoPeel := anisoPeel_of_valCount valuation_count
end DensInertW
