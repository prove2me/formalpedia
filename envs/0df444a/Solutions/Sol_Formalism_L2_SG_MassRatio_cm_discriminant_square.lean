-- Prove2me | solution 1 for Formalism.L2.SG.MassRatio.cm_discriminant_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:44.668873+00:00
-- url     : https://prove2.me/submissions/d4e31a6c-9962-4c2e-8e5c-895ffa03aedf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_SubMemDifferentIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_FinrankTwoOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CMDiscSq
import Theorems.Thm_PIW_CMDiscSq_discSq_of
import Theorems.Thm_PIW_CMDiscSq_relDegTwo
import Theorems.Thm_PIW_CMDiscSq_relDiffTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.L2.SG.MassRatio
theorem _root_.solution : Formalism.L2.SG.MassRatio.DiscSq :=
  PIW.CMDiscSq.discSq_of PIW.CMDiscSq.relDiffTop PIW.CMDiscSq.relDegTwo
end Formalism.L2.SG.MassRatio
