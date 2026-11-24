-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_exp_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:03.865863+00:00
-- url     : https://prove2.me/submissions/aee69825-b44f-43d3-9f59-714f8f9ccb06

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_row_le_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_std_iff
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
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I J : TIdx mu) (hI : StdT I) (hJ : StdT J)
    (h : qa_exp I = qa_exp J) : I = J := by
  funext c
  apply Subtype.ext
  have hrow : ∀ q, qa_row I c q = qa_row J c q := by
    intro q
    have hq : q.val < n := q.2.trans_le (colH_le mu c)
    have key : ∀ a, qa_row I c q ≤ a ↔ qa_row J c q ≤ a := by
      intro a
      rw [qa_row_le_iff, qa_row_le_iff]
      have h1 := qa_std_iff I hI c a ⟨q.val, hq⟩
      have h2 := qa_std_iff J hJ c a ⟨q.val, hq⟩
      rw [h] at h1
      exact h1.trans h2.symm
    exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
  rw [← Finset.map_orderEmbOfFin_univ (I c).1 (I c).2, ← Finset.map_orderEmbOfFin_univ (J c).1 (J c).2]
  ext x
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, (hrow q).symm⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, hrow q⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
