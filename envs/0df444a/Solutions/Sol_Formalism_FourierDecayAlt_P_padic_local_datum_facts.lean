-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.padic_local_datum_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:55:35.63051+00:00
-- url     : https://prove2.me/submissions/efd68e20-e862-46fa-b3dc-0e3d351ec27b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_datum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.DatumPadic := by
  intro p hp
  refine ⟨⟨Formalism.FourierDecayAlt.P.A5x7.stdChar p, Formalism.FourierDecayAlt.P.A5x7.datum p⟩, fun n hn => ?_⟩
  rw [isUnit_iff_ne_zero]
  exact_mod_cast hn
end Formalism.FourierDecayAlt.P
