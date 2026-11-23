-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:39.312384+00:00
-- url     : https://prove2.me/submissions/682b07f0-a4dc-4d90-b7a8-a94c03cb1b05

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge

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
variable {R : Type*} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (a : Fin n), a ∈ ql_U N D ↔ ∃ j, a ∈ D j
  | 0, _, a => by simp [ql_U]
  | N + 1, D, a => by
    rw [ql_U, mem_union, solution N, Fin.exists_fin_succ]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
