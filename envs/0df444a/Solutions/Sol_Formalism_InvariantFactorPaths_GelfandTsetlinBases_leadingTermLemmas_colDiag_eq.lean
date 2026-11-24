-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.colDiag_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:15.483007+00:00
-- url     : https://prove2.me/submissions/38818f6d-0020-4d17-9a13-ed3c8460c289

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_sum_emb
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_card_filter_lt_emb

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (r : Fin k → Fin n)
    (hr : ∀ i, (r i).val = i.val) : colDiag J = mon r (J.orderEmbOfFin h) 1 := by
  unfold colDiag mon
  rw [sum_emb J h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [card_filter_lt_emb, Finset.sum_eq_single (r i)]
  · rw [if_pos (hr i), Equiv.Perm.one_apply]
  · intro a _ ha
    rw [if_neg]
    intro hc
    exact ha (Fin.ext (by rw [hc, hr i]))
  · intro hc
    exact absurd (Finset.mem_univ _) hc
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
