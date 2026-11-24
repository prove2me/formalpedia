-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.torus_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:29.39346+00:00
-- url     : https://prove2.me/submissions/ad4acadd-09b2-4a01-8ccb-d0d528399a3f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_C
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_torus_X
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_prod_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable (A : Type*) [CommRing A]
variable {A}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (e : LVar ι ζ n →₀ ℕ) (a : A) :
    sharpHom isVec S (dt A n) (dti A n) (monomial e (AddMonoidAlgebra.single 0 a)) =
      monomial e (AddMonoidAlgebra.single (wt isVec S e) a) := by
  rw [monomial_eq, monomial_eq (a := AddMonoidAlgebra.single (wt isVec S e) a), map_mul, sharp_C, Finsupp.prod,
    map_prod]
  simp only [map_pow, torus_X, mul_pow, Finset.prod_mul_distrib, ← C_pow, AddMonoidAlgebra.single_pow, one_pow]
  rw [← map_prod C, prod_single, ← mul_assoc, ← C_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
