-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_commC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:28.162258+00:00
-- url     : https://prove2.me/submissions/e7000846-51ea-4228-beca-2aedde2c232e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_keepC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_comm_isoC

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
    (hP : IsTypeProj p LL j Cs T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) : ∀ x, P (Q x) = Q (P x) :=
  typeProj_comm_isoC LL j Cs T P hP Q (fun la => isoC_keepC LL j Cs la Q hQ)
end Formalism.InvariantFactorPaths.L4
