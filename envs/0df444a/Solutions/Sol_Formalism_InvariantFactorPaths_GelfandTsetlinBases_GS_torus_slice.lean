-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.torus_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:43.407107+00:00
-- url     : https://prove2.me/submissions/acd38b16-6440-4794-90d3-9fbdb93d6d26

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_monomial
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_torus_monomial

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
variable {k : Type*} [Field k] [Algebra k A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (Q : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    slc (cf (k := k) ν) (sharpHom isVec S (dt A n) (dti A n) (map (algebraMap A (TR A n)) Q)) =
      weightedHomogeneousComponent (wV isVec S) ν Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial e a =>
    have : algebraMap A (TR A n) a = AddMonoidAlgebra.single 0 a := rfl
    rw [map_monomial, this, torus_monomial, slc_monomial]
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_monomial, coeff_monomial]
    by_cases hd : e = d
    · subst hd
      rw [if_pos rfl, if_pos rfl]
      change (AddMonoidAlgebra.single (wt isVec S e) a).coeff ν = _
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · simp [hd]
  | add p q hp hq => simp only [map_add, hp, hq]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
