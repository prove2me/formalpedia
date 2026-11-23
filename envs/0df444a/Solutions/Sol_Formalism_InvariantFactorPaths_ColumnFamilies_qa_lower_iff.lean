-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_lower_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:46.096932+00:00
-- url     : https://prove2.me/submissions/4550c35d-044a-413c-99b0-c97b8afb0117

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Bl_general_b_fact_second_ter_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (Q : Fin n → Prop) [DecidablePred Q] (hQ : ∀ q q', q' ≤ q → Q q → Q q') (p : Fin n) :
    Q p ↔ p.val < (univ.filter Q).card := by
  first | exact Bl.general_b_fact_second_ter.goal1 .. | (apply Bl.general_b_fact_second_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter.goal1 <;> assumption)
end Formalism.InvariantFactorPaths.ColumnFamilies
