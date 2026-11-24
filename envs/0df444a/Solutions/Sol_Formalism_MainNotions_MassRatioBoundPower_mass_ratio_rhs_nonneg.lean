-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:41.240341+00:00
-- url     : https://prove2.me/submissions/c704f5be-55d3-4649-ae95-310773d4d159

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_lValEta_nonneg
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_one_le_two_vInv


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
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 ≤ Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by have := one_le_two_vInv (K := K); linarith
  exact mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (lValEta_nonneg hM)
end Formalism.MainNotions.MassRatioBoundPower
