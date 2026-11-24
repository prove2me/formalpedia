-- Prove2me | solution 1 for Formalism.REAL.exp_signature_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:37.693873+00:00
-- url     : https://prove2.me/submissions/7e7aae93-02d0-4452-9b7b-1d2393765b28

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_isUnit_signature_matrix
import Theorems.Thm_Formalism_REAL_signature_matrix_inv_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  have h := Matrix.exp_conj (Jm ε) A (isUnit_signature_matrix ε)
  rwa [signature_matrix_inv_self] at h
end Formalism.REAL
