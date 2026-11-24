-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_s_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:33:04.091056+00:00
-- url     : https://prove2.me/submissions/ae82879a-7c98-4d84-b873-ca345a2433cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_isUnit

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
theorem _root_.solution {A K : Finset (Fin n)} (h : Disjoint A K) : IsUnit (wedgeSign R A K) := by
  rw [wedgeSign, if_pos h]; exact ql_sr_isUnit A K
end Formalism.InvariantFactorPaths.ColumnFamilies
