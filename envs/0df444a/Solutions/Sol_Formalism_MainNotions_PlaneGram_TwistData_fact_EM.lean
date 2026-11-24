-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.fact_EM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:18.780886+00:00
-- url     : https://prove2.me/submissions/56ff96a3-80e4-4b37-bb88-6ec998224e16

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
theorem _root_.solution (ζ : D.EM) : fact ζ = (∏ b, ∏ a, (ζ (D.mb b, a)).factorial) *
    ((∏ t, ∏ a, (ζ (D.mlab t, a)).factorial) * ((∏ t, ∏ a, (ζ (D.mw t, a)).factorial) *
      ∏ t, ∏ a, (ζ (D.mtp t, a)).factorial)) := by
  unfold fact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type]
  rfl
end Formalism.MainNotions.PlaneGram.TwistData
