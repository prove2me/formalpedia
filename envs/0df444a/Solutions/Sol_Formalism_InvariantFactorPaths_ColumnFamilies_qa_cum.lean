-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_cum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:32:31.921866+00:00
-- url     : https://prove2.me/submissions/d61901c9-d6ce-4dce-b7f5-14319b11d49d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cnt_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_row_le_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (a p : Fin n) :
    ∑ b : Fin n with b ≤ a, qa_exp I (b, p) =
      (univ.filter fun c : ↥(TCols mu) => p.val < qa_cnt I c a).card := by
  simp only [qa_exp_apply]
  rw [Finset.sum_comm, Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ q : Fin (colH mu c),
      (∑ b : Fin n with b ≤ a, if qa_row I c q = b ∧ q.val = p.val then 1 else 0) =
        if (q.val = p.val ∧ q.val < qa_cnt I c a) then 1 else 0 := by
    intro q
    rw [Finset.sum_filter, Finset.sum_eq_single (qa_row I c q)]
    · have := qa_row_le_iff I c q a
      by_cases h : qa_row I c q ≤ a
      · simp [h, this.mp h]
      · have h' : ¬ q.val < qa_cnt I c a := fun hh => h (this.mpr hh)
        simp [h, h']
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp only [h1]
  split_ifs with hp
  · have hq : p.val < colH mu c := hp.trans_le (qa_cnt_le I c a)
    rw [Finset.sum_eq_single ⟨p.val, hq⟩]
    · simp [hp]
    · intro q _ hq'
      rw [if_neg]
      rintro ⟨h2, _⟩
      exact hq' (Fin.ext h2)
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h2, h3⟩
    exact hp (h2 ▸ h3)
end Formalism.InvariantFactorPaths.ColumnFamilies
