-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.euler_eq_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:41.011799+00:00
-- url     : https://prove2.me/submissions/6fdd38cd-0e81-4655-aac4-564e11670d11

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial


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
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)
  · rw [MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]
  · rw [map_add, mul_add, hP, hQ, map_add]
end Formalism.MainNotions.PlaneGram
