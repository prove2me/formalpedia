-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cge_digitPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:19.149029+00:00
-- url     : https://prove2.me/submissions/8bdcdda8-2ebf-4451-b432-491b2ab35885

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero


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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (ρ : D.Tau → Fin D.r → ℕ) {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (hG : cge v a G) : cge v a (D.digitPart p ρ G) := by
  unfold digitPart
  apply Formalism.MainNotions.PlaneGram.cge_sum v
  intro α _
  by_cases h : D.InClass p ρ α
  · rw [if_pos h]
    exact Formalism.MainNotions.PlaneGram.cge_monomial v _ (hG α)
  · rw [if_neg h]
    exact Formalism.MainNotions.PlaneGram.cge_zero v a
end Formalism.MainNotions.PlaneGram.TwistData
