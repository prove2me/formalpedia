-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.lValEta_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:09.170889+00:00
-- url     : https://prove2.me/submissions/32dc53a4-c5b0-405d-b3a8-c91d0e82f116

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_eulerFac_le
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_two_le_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M :=
  tprod_nonneg fun P => (eulerFac_le hM P.1 (by haveI := P.2; exact two_le_absNorm P.1)).1.le
end Formalism.MainNotions.MassRatioBoundPower
