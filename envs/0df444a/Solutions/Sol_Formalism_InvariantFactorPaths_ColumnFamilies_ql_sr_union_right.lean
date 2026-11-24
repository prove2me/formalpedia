-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_union_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:02.835846+00:00
-- url     : https://prove2.me/submissions/5f5400ec-f9ec-4321-90be-69cb3ecaf54b

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
theorem _root_.solution (A : Finset (Fin n)) {B C : Finset (Fin n)} (h : Disjoint B C) :
    ql_sr R A (B ∪ C) = ql_sr R A B * ql_sr R A C := by
  simp only [ql_sr, prod_union h, prod_mul_distrib]
end Formalism.InvariantFactorPaths.ColumnFamilies
