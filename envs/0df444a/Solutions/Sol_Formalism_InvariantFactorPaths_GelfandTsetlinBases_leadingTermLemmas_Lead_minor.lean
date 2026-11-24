-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.Lead_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:55.500528+00:00
-- url     : https://prove2.me/submissions/2bbf7676-e7c0-4e01-8a39-5328e9dbbe3f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_det
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_card_initSeg
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_initSeg_emb
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
theorem _root_.solution (k : Type*) [CommRing k] (J : Finset (Fin n)) :
    Lead key (minorF (genX k n) (initSeg n J.card) J) (colDiag J) := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  have hcard : J.card = (initSeg n J.card).card := (card_initSeg hle).symm
  unfold minorF
  rw [dif_pos hcard, colDiag_eq J hcard ((initSeg n J.card).orderEmbOfFin rfl)
    (fun i => initSeg_emb hle rfl i)]
  exact Lead_det k _ _ (OrderEmbedding.strictMono _) (OrderEmbedding.strictMono _)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
