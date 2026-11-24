-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.path_basis_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:46.45492+00:00
-- url     : https://prove2.me/submissions/09db65c1-1663-49f8-a741-34973c4a975c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_linearIndependent_of_Lead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_key_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_tab_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_tab

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
open leadingTermLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : LemmaA := by
  intro k _ n C
  refine linearIndependent_of_Lead key_inj _ (fun T => tabDiag T.1) ?_ (fun T => Lead_tab k T.1)
  intro T T' h
  exact Subtype.ext (tab_inj T.2 T'.2 h)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
