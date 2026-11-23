-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.XDXD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:03.855895+00:00
-- url     : https://prove2.me/submissions/023829fb-1b5f-47f9-b06e-977a6e3460bc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (u v : σ) (huv : u ≠ v) (z : MvPolynomial σ k) (cu cv : k) (hu : X u * pderiv u z = cu • z)
    (hv : X v * pderiv v z = cv • z) : X v * pderiv u (X u * pderiv v z) = (cv * (cu + 1)) • z := by
  classical
  have h1 : pderiv u (X v * pderiv v z) = X v * pderiv u (pderiv v z) := by
    rw [pderiv_mul, pderiv_X, Pi.single_eq_of_ne (Ne.symm huv)]
    simp
  have h2 : X u * (X v * pderiv u (pderiv v z)) = (cv * cu) • z := by
    rw [← h1, hv, Derivation.map_smul, mul_smul_comm, hu, smul_smul]
  rw [pderiv_mul, pderiv_X, Pi.single_eq_same, one_mul, mul_add, hv, mul_left_comm, h2, ← add_smul]
  congr 1
  ring
end Formalism.InvariantFactorPaths.L4
