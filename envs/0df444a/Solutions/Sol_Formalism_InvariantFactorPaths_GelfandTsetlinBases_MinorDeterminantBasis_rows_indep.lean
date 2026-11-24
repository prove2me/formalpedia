-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.rows_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:48:00.003658+00:00
-- url     : https://prove2.me/submissions/82043c0f-bd3f-408f-ba17-48d8e773a160

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace MinorDeterminantBasis
section Abstract
variable {σ X : Type} [Fintype X] [DecidableEq X]
private theorem sum_smul_sum_smul_eq_sum_mul_smul {S : Type} [CommRing S] (M : Matrix X X S) (e : X → MvPolynomial σ S)
    (g : X → S) : ∑ x, g x • ∑ y, M x y • e y = ∑ y, (∑ x, g x * M x y) • e y := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm
end Abstract
end MinorDeterminantBasis
open MinorDeterminantBasis
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
variable {σ X : Type} [Fintype X] [DecidableEq X]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
theorem _root_.solution (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S]
    (h : LinearIndependent S fun x => MvPolynomial.map (Int.castRingHom S) (F x)) :
    LinearIndependent S ((cmat m F).map (Int.castRingHom S)).row := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  apply h g
  simp only [expand m hm F hF S, sum_smul_sum_smul_eq_sum_mul_smul]
  have hy : ∀ y, ∑ x, g x * ((cmat m F).map (Int.castRingHom S)) x y = 0 := by
    intro y
    have := congrFun hg y
    simpa [Finset.sum_apply, Matrix.row] using this
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [hy y, zero_smul]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
