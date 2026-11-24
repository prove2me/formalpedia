-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:05.597864+00:00
-- url     : https://prove2.me/submissions/1865af80-c961-4c02-9561-d575232ea517

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_P

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
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) :
    Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)) ≤
      (dualWeyl ℚ n n (qd_nu mu)).map (qd_L mu) := by
  rw [Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact ⟨qd_P mu I, tableauBideterminant_mem_dualWeyl' mu I, qd_L_P mu I⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
