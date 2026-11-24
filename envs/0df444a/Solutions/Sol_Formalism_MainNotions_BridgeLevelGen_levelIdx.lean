-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGen.levelIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:52:07.040403+00:00
-- url     : https://prove2.me/submissions/136aad34-d505-4749-bbc1-fd3332826f92

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGen_levelGen_holds
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_levelIdx_holds


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
theorem _root_.solution (I : AutInst) (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) :=
  levelIdx_holds μf hg (levelGen_holds I g hg)
end Formalism.MainNotions.BridgeLevelGen
