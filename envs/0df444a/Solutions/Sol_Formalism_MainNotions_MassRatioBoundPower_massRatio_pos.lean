-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.massRatio_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:57.044728+00:00
-- url     : https://prove2.me/submissions/ac34f41c-a4c2-43c2-8494-dc54c7b4ac06

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_lValEta_ge
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
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv K := one_le_two_vInv
  have hv0 : 0 < Formalism.HermitianLatticesTheory.vInv K := by linarith
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta K M := lt_of_lt_of_le (Real.exp_pos _) (lValEta_ge hM)
  have hb : 0 < Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) := Real.sqrt_pos.2 (by positivity)
  have hf : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact mul_pos (div_pos (by positivity) hb) hL
end Formalism.MainNotions.MassRatioBoundPower
