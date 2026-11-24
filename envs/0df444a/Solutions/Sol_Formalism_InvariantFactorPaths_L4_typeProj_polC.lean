-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_polC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:08.253396+00:00
-- url     : https://prove2.me/submissions/b3c3826b-f152-4e39-af89-ad8552bf2388

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_eulC
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) : ∀ x ∈ Pol p r LL, P x ∈ Pol p r LL := by
  intro x hx
  rw [pol_iff_eul] at hx ⊢
  intro i
  rw [← typeProj_eulC LL j Cs T P hP i, hx i, map_smul]
end Formalism.InvariantFactorPaths.L4
