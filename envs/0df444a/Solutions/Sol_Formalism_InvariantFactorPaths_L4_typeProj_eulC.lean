-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_eulC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:53.947287+00:00
-- url     : https://prove2.me/submissions/9cfef36a-5f63-4785-8530-c46a3cc82bf3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_commC
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct


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
    (hP : IsTypeProj p LL j Cs T P) (i0 : Fin N) :
    ∀ x, P (ProjS.eulL (fun c : Fin r => (i0, c)) x) = ProjS.eulL (fun c : Fin r => (i0, c)) (P x) :=
  typeProj_commC LL j Cs T P hP _ (fun c _ d _ x => eul_glAct LL j i0 c d x)
end Formalism.InvariantFactorPaths.L4
