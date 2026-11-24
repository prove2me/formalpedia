-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.colDiag_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:09.884261+00:00
-- url     : https://prove2.me/submissions/fb72e8ed-75bb-490b-a302-5e2f672bdef0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mon_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_nthElt_emb
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_lt_card_of_nthElt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_colDiag_eq

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
theorem _root_.solution (J : Finset (Fin n)) (a b : Fin n) :
    colDiag J (a, b) = if nthElt J a.val = b.val then 1 else 0 := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  rw [colDiag_eq J rfl (fun i => (⟨i.val, lt_of_lt_of_le i.2 hle⟩ : Fin n)) (fun _ => rfl), mon_apply]
  by_cases hab : nthElt J a.val = b.val
  · rw [if_pos hab]
    have ha : a.val < J.card := lt_card_of_nthElt (by rw [hab]; exact b.2)
    rw [Finset.sum_eq_single ⟨a.val, ha⟩]
    · rw [if_pos]
      refine ⟨Fin.ext rfl, ?_⟩
      apply Fin.ext
      rw [Equiv.Perm.one_apply]
      simp only
      rw [← hab]
      exact (nthElt_emb rfl ⟨a.val, ha⟩).symm
    · intro i _ hi
      rw [if_neg]
      rintro ⟨h1, _⟩
      have h3 := congrArg Fin.val h1
      exact hi (Fin.ext h3)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hab
    have h3 : a.val = i.val := (congrArg Fin.val h1).symm
    rw [h3, nthElt_emb rfl i]
    exact congrArg Fin.val h2
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
