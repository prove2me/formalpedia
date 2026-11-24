-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.tab_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:14.262846+00:00
-- url     : https://prove2.me/submissions/8e9b7376-c0b7-4d17-86b1-f5779b95f525

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_nthElt_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mem_iff_nthElt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_tabDiag_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_semi_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mono_eq_of_counts

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
variable {n C : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {T T' : Fin C → Finset (Fin n)} (hT : SemiStd T) (hT' : SemiStd T')
    (h : tabDiag T = tabDiag T') : T = T' := by
  have hrow : ∀ a : Fin n, (fun c => nthElt (T c) a.val) = fun c => nthElt (T' c) a.val := by
    intro a
    apply mono_eq_of_counts (n := n) _ _ (semi_mono hT a.val) (semi_mono hT' a.val)
      (fun c => nthElt_le _ _) (fun c => nthElt_le _ _)
    intro v hv
    have h1 := tabDiag_apply T a ⟨v, hv⟩
    have h2 := tabDiag_apply T' a ⟨v, hv⟩
    rw [h, h2] at h1
    exact h1.symm
  funext c
  ext b
  rw [mem_iff_nthElt, mem_iff_nthElt]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; exact (congr_fun (hrow a) c).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; exact congr_fun (hrow a) c⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
