-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenB.val_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:44:00.915991+00:00
-- url     : https://prove2.me/submissions/8df78764-b52a-4a01-afce-37c3880085cc

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.MainNotions.BridgeLevelGenB
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = v.intValuation a := by
  rw [PI.WAU.val_algebraMap_F, valuation_of_algebraMap]
end Formalism.MainNotions.BridgeLevelGenB
