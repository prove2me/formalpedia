-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_exists_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:32:41.762041+00:00
-- url     : https://prove2.me/submissions/12af0f5c-7bf7-46bc-97ab-fe3f744822fc

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_eq_of_psi

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
theorem _root_.solution (s : Finset (Fin n → ℤ)) (hs : s.Nonempty) :
    ∃ nu ∈ s, ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  obtain ⟨nu, hnu, hmax⟩ := s.exists_max_image qb_psi hs
  exact ⟨nu, hnu, fun mu hmu hle => (qb_eq_of_psi hle (hmax mu hmu)).symm⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
