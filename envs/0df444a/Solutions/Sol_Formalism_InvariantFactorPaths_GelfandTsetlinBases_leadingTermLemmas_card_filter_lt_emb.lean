-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.card_filter_lt_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:34.488858+00:00
-- url     : https://prove2.me/submissions/a4366e91-1da2-4d13-8483-bbf808528ba6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Bl_general_b_fact_right_further_goal1


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
theorem _root_.solution (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (i : Fin k) :
    (J.filter (· < J.orderEmbOfFin h i)).card = i.val := by
  first | exact Bl.general_b_fact_right_further.goal1 .. | (apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_further.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_further.goal1 n J k h i | exact @Bl.general_b_fact_right_further.goal1 n J k h | exact @Bl.general_b_fact_right_further.goal1 n J k | exact @Bl.general_b_fact_right_further.goal1 n J | exact @Bl.general_b_fact_right_further.goal1 n
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
