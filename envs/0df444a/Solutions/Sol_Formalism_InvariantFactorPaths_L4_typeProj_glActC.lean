-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_glActC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:33.543716+00:00
-- url     : https://prove2.me/submissions/a5dad8a7-a1e7-490c-bd4e-2d14bbc9d885

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_glStableC
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
    (hP : IsTypeProj p LL j Cs T P) (c : Fin r) (hc : c ∈ Cs) (d : Fin r) (hd : d ∈ Cs) :
    ∀ x, P (glAct p LL j c d x) = glAct p LL j c d (P x) :=
  typeProj_comm_isoC LL j Cs T P hP _ (fun la => isoC_glStableC LL j Cs la c hc d hd)
end Formalism.InvariantFactorPaths.L4
