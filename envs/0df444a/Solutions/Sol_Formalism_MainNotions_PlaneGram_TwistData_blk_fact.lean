-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.blk_fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:24.152479+00:00
-- url     : https://prove2.me/submissions/0d07f701-6be4-48f5-8c59-292fb6064675

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_output_exponent_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_kapL_dUp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_eIn_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_out_mul_in
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_lower
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_upper
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_mul
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
theorem _root_.solution (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ ζ' : D.EM} (h : D.GoodE p ζ) (hb : D.SameBlockAlt ζ ζ') :
    vN v (fact ζ') - vN v (fact ζ) ≤ D.kapD p := by
  have hp := two_le_p hD
  rw [fact_eq_out_mul_in D.outP ζ, fact_eq_out_mul_in D.outP ζ', D.output_exponent_same_block hb,
    vN_mul hD (fact_ne_zero _) (fact_ne_zero _), vN_mul hD (fact_ne_zero _) (fact_ne_zero _)]
  have e1 : ∀ i, ldeg (eIn D.outP ζ') i = ldeg (eIn D.outP ζ) i := by
    intro i; rw [ldeg_eIn, ldeg_eIn, hb.1 i]
  have h1 := fact_upper hD e1
  have h2 := fact_lower hD (α := eIn D.outP ζ) (d := fun i => ldeg (eIn D.outP ζ) i) (fun _ => rfl)
  have h3 : kapL p D.r (fun i => ldeg (eIn D.outP ζ) i) ≤ kapL p D.r D.dUp :=
    kapL_mono hp D.r (D.ldeg_eIn_le (by omega) h)
  have h4 := kapL_le_kap' hp hr D.dO
  rw [D.kapL_dUp] at h3
  have h5 : D.kapD p = kap p D.r D.dO := rfl
  rw [h5]; linarith
end Formalism.MainNotions.PlaneGram.TwistData
