-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:42.958203+00:00
-- url     : https://prove2.me/submissions/9bd3f808-6572-47f1-aebe-67bf91e209bd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_mul

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    vN v (∏ i ∈ s, f i) = ∑ i ∈ s, vN v (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [vN_one hD]
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      vN_mul hD (hf i (by simp)) (Finset.prod_ne_zero_iff.mpr fun j hj => hf j (by simp [hj])),
      ih fun j hj => hf j (by simp [hj])]
end Formalism.MainNotions.PlaneGram
