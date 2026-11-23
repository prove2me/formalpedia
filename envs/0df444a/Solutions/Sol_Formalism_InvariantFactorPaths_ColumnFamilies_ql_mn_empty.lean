-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_mn_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:32.284623+00:00
-- url     : https://prove2.me/submissions/29f92e7c-39d8-4622-97e9-265b93cd9a50

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_ne


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
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (K : Finset (Fin n)) : qs_mn g K ∅ = if K = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp
  · exact qs_mn_ne g (by simpa using h)
end Formalism.InvariantFactorPaths.ColumnFamilies
