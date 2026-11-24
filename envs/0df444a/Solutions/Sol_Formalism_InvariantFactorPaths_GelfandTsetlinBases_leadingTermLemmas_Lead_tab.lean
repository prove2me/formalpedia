-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.Lead_tab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:56.658926+00:00
-- url     : https://prove2.me/submissions/e0c16c24-cafc-4ce0-a791-14713fc82190

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_key_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_minor
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_tabDiag_eq

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
theorem _root_.solution (k : Type*) [CommRing k] (T : Fin C → Finset (Fin n)) :
    Lead key (tabMinors k T) (tabDiag T) := by
  rw [tabDiag_eq]
  unfold tabMinors
  exact Lead_prod key_inj _ _ _ fun c _ => Lead_minor k (T c)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
