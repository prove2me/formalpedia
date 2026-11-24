-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_cofactor_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:10.865312+00:00
-- url     : https://prove2.me/submissions/f2c90cf5-4b56-4b9d-bec0-e9a243b0e93a

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_cofactor_corner_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.GramCofactor := by
  intro V _ _ B r f x' T' h
  unfold C7.cofX'
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.map_smulₛₗ, h]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [cofactor_corner_identity r (C7.zhat B f x')]
  rw [← Complex.mul_conj]
  ring
end Formalism.FourierDecayAlt.P
