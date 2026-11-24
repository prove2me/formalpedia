-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.vge_coeff_GM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:42:53.958796+00:00
-- url     : https://prove2.me/submissions/0e4ab90d-078e-4704-a440-d27f69ab867e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_coeff_GM
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_of_bge
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_unit


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
    (hF : F ∈ PolK K D.r D.dO) (hF0 : bge v 0 F) (ζ : D.EM) :
    vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ)) := by
  rw [coeff_GM]
  have a1 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ))).2.1
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 : vge v (-D.n0 v) (F.coeff (D.phE p ζ)) := by
    have := cge_of_bge hD hF hF0 (D.phE p ζ)
    rw [zero_sub] at this; exact this
  have a4 := vge_natCast v (∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x))
  have := vge_mul v a1 (vge_mul v (vge_mul v a2 a3) a4)
  exact vge_mono v (by linarith) this
end Formalism.MainNotions.PlaneGram.TwistData
