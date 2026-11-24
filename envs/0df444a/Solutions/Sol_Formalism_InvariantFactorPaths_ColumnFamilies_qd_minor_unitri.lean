-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_minor_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:26.412878+00:00
-- url     : https://prove2.me/submissions/830fb14b-36a0-45cb-b9f3-ddb12f4497ef

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_can_emb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (c : ↥(TCols mu))
    (J : {J : Finset (Fin n) // J.card = colH mu c}) :
    evGL u (minorC J.1 (canT mu c).1 J.2 (canT mu c).2) = if J = canT mu c then 1 else 0 := by
  rw [qb_evGL_minorC]
  split_ifs with hJ
  · subst hJ
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro a b hab
      exact h2 _ _ ((OrderEmbedding.lt_iff_lt _).2 hab)
  · obtain ⟨j, hjJ, hj⟩ : ∃ j ∈ J.1, colH mu c ≤ j.val := by
      by_contra hcon
      push Not at hcon
      apply hJ
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        exact (qb_mem_canT mu c j).2 (hcon j hj)
      · rw [J.2, (canT mu c).2]
    have hr : j ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hjJ
    obtain ⟨a, ha⟩ := hr
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, ha, qd_can_emb]
    apply h2
    exact Fin.lt_def.2 (lt_of_lt_of_le (show (Fin.castLE (colH_le mu c) b).val < colH mu c from b.2) hj)
end Formalism.InvariantFactorPaths.ColumnFamilies
