-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:02.942084+00:00
-- url     : https://prove2.me/submissions/8c612bff-add2-484a-aa9c-9e6bcb68deba

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le


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
variable {K : Type} [Field K] {L L' : Type} {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [DecidableEq L] (sg : L → Bool) (S : Finset L) {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (L × Fin r) K) :
    ∑ k ∈ s, valS sg S (f k) ≤ valS sg S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    simp [valS, lord, MvPolynomial.support_one]
    intro b hb a ha
    rw [MvPolynomial.coeff_one] at hb ha
    split_ifs at hb ha with hb0
    · rw [AddMonoidAlgebra.one_def] at ha
      unfold AddMonoidAlgebra.single at ha
      simp at ha
      rw [Finsupp.single_apply] at ha
      split_ifs at ha with ha0
      · subst ha0
        simp
      · exact absurd rfl ha
    · exact absurd rfl hb
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add le_rfl ih).trans (by apply valS_mul_le)
end Formalism.MainNotions.PlaneGram
