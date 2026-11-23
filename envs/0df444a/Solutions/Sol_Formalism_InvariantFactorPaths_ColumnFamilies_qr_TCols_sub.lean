-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_TCols_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:14.783695+00:00
-- url     : https://prove2.me/submissions/8e4c744a-7cfc-44bf-8fe7-58deea0405cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lastIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lam_last_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_nu_zero_le

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
theorem _root_.solution (hi : Interl lam nu) {c : ℤ} (hc : c ∈ TCols nu) : c ∈ TCols lam := by
  simp only [TCols, Finset.mem_Ioc, qr_lastIdx] at hc ⊢
  exact ⟨lt_of_le_of_lt (qr_lam_last_le hi) hc.1, hc.2.trans (qr_nu_zero_le hi)⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
