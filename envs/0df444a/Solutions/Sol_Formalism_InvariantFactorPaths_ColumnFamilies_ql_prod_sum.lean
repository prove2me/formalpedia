-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.41218+00:00
-- url     : https://prove2.me/submissions/6a21f574-0997-4a4f-9ec4-4db74287eb37

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
theorem _root_.solution {N : ℕ} (G : Fin N → Finset (Fin n) → R) :
    ∏ j, ∑ a, G j a = ∑ x : Fin N → Finset (Fin n), ∏ j, G j (x j) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
end Formalism.InvariantFactorPaths.ColumnFamilies
