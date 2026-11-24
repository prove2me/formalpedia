-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sW_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:33.172821+00:00
-- url     : https://prove2.me/submissions/3b87df43-0d70-4601-b726-05ce94d7804e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_U
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_isUnit


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
theorem _root_.solution : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
    IsUnit (ql_sW R N D)
  | 0, _, _ => by simp [ql_sW]
  | N + 1, D, h => by
    rw [ql_sW]
    refine IsUnit.mul (ql_s_isUnit ?_) (solution N _ fun i j hij => h _ _ (by simpa using hij))
    rw [Finset.disjoint_left]
    intro a ha hU
    obtain ⟨j, hj⟩ := (ql_mem_U N _ a).1 hU
    exact Finset.disjoint_left.1 (h 0 j.succ (Fin.succ_ne_zero j).symm) ha hj
end Formalism.InvariantFactorPaths.ColumnFamilies
