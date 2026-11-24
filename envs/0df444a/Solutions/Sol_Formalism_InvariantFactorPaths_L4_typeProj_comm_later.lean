-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_comm_later
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:44.56513+00:00
-- url     : https://prove2.me/submissions/ba5af367-e8f7-4e40-b3e7-456277c81d79

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_commC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_glActC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_split
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_comm

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
theorem _root_.solution (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
  rw [glAct_split LL j j' c d, LinearMap.add_apply, LinearMap.add_apply, map_add,
    typeProj_glActC LL j univ T P hP c (Finset.mem_univ _) d (Finset.mem_univ _) x,
    typeProj_commC LL j univ T P hP (glRest p LL j j' c d) (fun a _ b _ y => glRest_comm LL j j' hjj c d a b y) x]
end Formalism.InvariantFactorPaths.L4
