-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.factorial_embedded_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:21.489728+00:00
-- url     : https://prove2.me/submissions/337de689-37c1-42b6-8653-3e4221cbf006

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory

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
omit [CharZero K]
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) : fact (D.collapseExponent p ζ) = (∏ b, ∏ a, (ζ (D.mb b, a)).factorial) *
    ∏ t, ∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial := by
  unfold fact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type]
  simp [collapseExponent]
end Formalism.MainNotions.PlaneGram.TwistData
