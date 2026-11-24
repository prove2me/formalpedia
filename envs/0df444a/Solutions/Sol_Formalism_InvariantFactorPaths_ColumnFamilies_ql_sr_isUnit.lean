-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.658238+00:00
-- url     : https://prove2.me/submissions/c9a763f8-f443-4112-b2e3-ca3e84525645

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
theorem _root_.solution (A K : Finset (Fin n)) : IsUnit (ql_sr R A K) := by
  unfold ql_sr
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun k _ => ?_
  split_ifs
  · exact isUnit_one.neg
  · exact isUnit_one
end Formalism.InvariantFactorPaths.ColumnFamilies
