-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.kapD_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:19.920467+00:00
-- url     : https://prove2.me/submissions/d4b0b9fb-9d3e-466e-a624-74e135d16cec

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kap_ge_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) (hJ : 1 ≤ D.J) : 1 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  have h1 : 1 ≤ Fintype.card D.OL := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have : 1 ≤ D.J * D.r := Nat.mul_pos hJ hr
    omega
  have h2 : (1 : ℝ) ≤ (Fintype.card D.OL : ℝ) := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ (D.r : ℝ) := by exact_mod_cast hr
  nlinarith
end Formalism.MainNotions.PlaneGram.TwistData
