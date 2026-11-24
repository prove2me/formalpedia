-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_can_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.105746+00:00
-- url     : https://prove2.me/submissions/844a672b-883f-4358-8b35-9ecf01724f34

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colH_succ_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (c : ℤ) : (qr_can nu (c + 1)).1 ⊆ (qr_can nu c).1 := by
  intro x hx
  simp only [qr_can, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le nu c)⟩, rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
