-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_union_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.682223+00:00
-- url     : https://prove2.me/submissions/ead22c85-aa35-4aa0-bbb2-4d1891e24136

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
theorem _root_.solution {A B : Finset (Fin n)} (h : Disjoint A B) (C : Finset (Fin n)) :
    ql_sr R (A ∪ B) C = ql_sr R A C * ql_sr R B C := prod_union h
end Formalism.InvariantFactorPaths.ColumnFamilies
