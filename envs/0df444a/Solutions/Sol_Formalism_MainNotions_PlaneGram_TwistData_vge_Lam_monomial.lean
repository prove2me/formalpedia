-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.vge_Lam_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:39.196799+00:00
-- url     : https://prove2.me/submissions/539a4395-760d-44af-960b-3d1515706099

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_phE_lower
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_unit
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_vN


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
theorem _root_.solution (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF0 : bge v 0 F) {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.n0 v - D.kapD p / 2) (D.abelian₂ p F (monomial ζ 1)) := by
  rw [Lam_monomial]
  have a1 := hF0 (D.phE p ζ)
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 := vge_vN hD (fact_ne_zero (D.phE p ζ))
  have a4 := D.fact_phE_lower hD hV.1 hζ
  have := vge_mul v (vge_mul v a1 (vge_mul v a2 (vge_one v))) a3
  exact vge_mono v (by linarith) this
end Formalism.MainNotions.PlaneGram.TwistData
