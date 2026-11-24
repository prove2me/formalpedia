-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.good_Pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:35.105163+00:00
-- url     : https://prove2.me/submissions/0409a750-7fc0-420f-b62e-1d01dd9f9463

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_linMap_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_GoodE_good_exponent_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_sum


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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by
  rw [linMap_eq_sum Pj Y]
  refine TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _
  intro ζ' hζ'
  exact TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')
end Formalism.MainNotions.PlaneGram
