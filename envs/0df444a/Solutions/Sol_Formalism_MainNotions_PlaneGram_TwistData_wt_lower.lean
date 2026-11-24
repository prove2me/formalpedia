-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.wt_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:38:52.266885+00:00
-- url     : https://prove2.me/submissions/9a49f002-d114-45ff-853b-7ca5a5c1dfe6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_phE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_lower
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_kapL_le_kap__2a6ba908208b


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
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ : D.EM} (h : D.GoodE p ζ) :
    2 * D.n0 v - 2 * D.kapD p ≤ vN v (fact (D.collapseExponent p ζ)) + vN v (fact (D.tpE ζ)) := by
  have hp := two_le_p hD
  have h1 := fact_add_lower hD (α := D.collapseExponent p ζ) (α' := D.tpE ζ) (d := D.dO) (D.ldeg_phE p ζ h)
  have h4 := kapL_le_kap' hp hr D.dO
  have h5 : D.kapD p = kap p D.r D.dO := rfl
  have h6 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
  rw [h5, h6]; linarith
end Formalism.MainNotions.PlaneGram.TwistData
