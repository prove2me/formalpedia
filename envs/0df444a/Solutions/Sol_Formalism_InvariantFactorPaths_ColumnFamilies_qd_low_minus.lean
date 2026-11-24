-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_low_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:59.505273+00:00
-- url     : https://prove2.me/submissions/5bf1d007-385a-4f12-b8e9-e5cd1decaaeb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_antisymm
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : DomLowerSet (qd_low mu \ {mu}) := by
  refine ⟨fun la hla => hla.1.1, fun la hla nu hnu hle => ⟨⟨hnu, qb_domLE_trans hle hla.1.2⟩, ?_⟩⟩
  intro h
  rw [Set.mem_singleton_iff] at h
  subst h
  exact hla.2 (qb_domLE_antisymm hla.1.2 hle)
end Formalism.InvariantFactorPaths.ColumnFamilies
