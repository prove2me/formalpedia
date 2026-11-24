-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.441354+00:00
-- url     : https://prove2.me/submissions/c26d13c5-c6f8-4420-819a-1b2575af4499

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
theorem _root_.solution (A K : Finset (Fin n)) : ((ql_sr ℤ A K : ℤ) : R) = ql_sr R A K := by
  simp only [ql_sr, Int.cast_prod]
  refine prod_congr rfl fun a _ => prod_congr rfl fun k _ => ?_
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.ColumnFamilies
