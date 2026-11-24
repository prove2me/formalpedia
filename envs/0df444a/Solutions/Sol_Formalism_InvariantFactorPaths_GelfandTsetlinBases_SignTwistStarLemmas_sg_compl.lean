-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.sg_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:48:32.489903+00:00
-- url     : https://prove2.me/submissions/7ef93fbb-d2e6-47ca-9cb9-2e5a5eae1ec7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_neg_one_pow_eq_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (J : Finset (Fin n)) (m : Fin n) : sg Jᶜ m * sg J m = (-1) ^ (n + 1 + m.val) := by
  unfold sg
  rw [← pow_add]
  have h1 : (Jᶜ.filter fun j => m < j).card + (J.filter fun j => m < j).card = n - 1 - m.val := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_compl_add_sum, ← Finset.card_filter, ← Fin.card_Ioi]
    congr 1
    ext x
    simp
  rw [h1]
  apply neg_one_pow_eq_of
  have := m.2
  exact ⟨n, by omega⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
