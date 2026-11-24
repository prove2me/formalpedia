-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:47.471409+00:00
-- url     : https://prove2.me/submissions/f56bec91-4c69-4f38-9558-5d456ec041dc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_prod_laurent_T

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
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : LVar ι ζ n →₀ ℕ) (c : L) :
    tw isVec S g gi last (monomial e c) =
      LaurentPolynomial.T (wExp isVec S last e) * LaurentPolynomial.C (sharpHom isVec S g gi (monomial e c)) := by
  have e1 : sharpHom isVec S g gi (monomial e c) =
      C c * ∏ x ∈ e.support, (sharpHom isVec S g gi (X x)) ^ (e x) := by
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    simp [sharpHom]
  rw [e1, tw, coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, LaurentPolynomial.T_pow, prod_laurent_T, map_mul, map_prod, map_pow,
    wExp, RingHom.comp_apply]
  ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
