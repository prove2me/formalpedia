-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mem_iff_nthElt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.137621+00:00
-- url     : https://prove2.me/submissions/36ec8cae-1c38-4899-8c4d-8cb5de8e1709

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_nthElt_emb
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_lt_card_of_nthElt

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
theorem _root_.solution (J : Finset (Fin n)) (b : Fin n) : b ∈ J ↔ ∃ a : Fin n, nthElt J a.val = b.val := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  constructor
  · intro hb
    have : b ∈ Set.range (J.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨i, hi⟩ := this
    refine ⟨⟨i.val, lt_of_lt_of_le i.2 hle⟩, ?_⟩
    simp only
    rw [nthElt_emb rfl i, hi]
  · rintro ⟨a, ha⟩
    have hlt : a.val < J.card := lt_card_of_nthElt (by rw [ha]; exact b.2)
    have h1 := nthElt_emb (J := J) rfl ⟨a.val, hlt⟩
    simp only at h1
    rw [ha] at h1
    rw [Fin.ext h1]
    exact Finset.orderEmbOfFin_mem _ _ _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
