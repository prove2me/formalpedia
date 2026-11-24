-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_exists_max_above
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:40:59.809046+00:00
-- url     : https://prove2.me/submissions/c9401578-bdc1-4bb4-95db-4758521751a1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_exists_max

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (s : Finset (Fin n → ℤ)) {mu0 : Fin n → ℤ} (h0 : mu0 ∈ s) :
    ∃ nu ∈ s, DomLE mu0 nu ∧ ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  classical
  obtain ⟨nu, hnu, hmax⟩ := qb_exists_max (s.filter fun mu => DomLE mu0 mu)
    ⟨mu0, by simp [h0, qb_domLE_refl]⟩
  rw [mem_filter] at hnu
  exact ⟨nu, hnu.1, hnu.2, fun mu hmu hle =>
    hmax mu (by rw [mem_filter]; exact ⟨hmu, qb_domLE_trans hnu.2 hle⟩) hle⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
