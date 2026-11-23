-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:33.342052+00:00
-- url     : https://prove2.me/submissions/cea9f850-943d-4249-bc84-45fa0c883784

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn

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
theorem _root_.solution (A : Finset (Fin n)) (m : Fin n) : ql_sr R A {m} = ((qs_sg A m : ℤ) : R) := by
  simp only [ql_sr, prod_singleton, qs_sg]
  rw [prod_ite]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
