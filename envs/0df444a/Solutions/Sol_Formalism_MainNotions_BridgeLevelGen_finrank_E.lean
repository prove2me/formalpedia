-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGen.finrank_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:02:31.011432+00:00
-- url     : https://prove2.me/submissions/a04ad612-b7b8-4da0-986b-4dce3690e854

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGen
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct
namespace Formalism.MainNotions.BridgeLevelGen
theorem _root_.solution (I : AutInst) : Module.finrank ℚ I.E = 2 * I.f := by
  rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show _ = 2 * Module.finrank ℚ I.F
  ring
end Formalism.MainNotions.BridgeLevelGen
