-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_prod_leadingMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:17.303799+00:00
-- url     : https://prove2.me/submissions/c97ab5a8-82a8-4a16-ab3f-9a02dab77a10

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_can_emb
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
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) :
    qd_P mu (canT mu) = ∏ c : ↥(TCols mu), lpMinor ℚ (colH mu c) (colH_le mu c) (colH_le mu c) := by
  unfold qd_P
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor lpMinor
  simp only [qd_can_emb]
end Formalism.InvariantFactorPaths.ColumnFamilies
