-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:39.456927+00:00
-- url     : https://prove2.me/submissions/c28b2e9b-9236-4608-954b-4e88d58d81f0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
variable {σ X : Type} [Fintype X] [DecidableEq X]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
theorem _root_.solution (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S] (x : X) :
    MvPolynomial.map (Int.castRingHom S) (F x) =
      ∑ y, ((cmat m F).map (Int.castRingHom S)) x y • monomial (m y) (1 : S) := by
  classical
  ext d
  rw [coeff_map, MvPolynomial.coeff_sum]
  simp only [coeff_smul, coeff_monomial, Matrix.map_apply, cmat, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hd : d ∈ Set.range m
  · obtain ⟨y₀, rfl⟩ := hd
    rw [Finset.sum_eq_single y₀]
    · simp
    · intro y _ hy
      rw [if_neg (hm.ne hy)]
    · simp
  · have h0 : coeff d (F x) = 0 := by
      by_contra h
      exact hd (hF x d (mem_support_iff.mpr h))
    rw [h0, map_zero, Finset.sum_eq_zero]
    intro y _
    rw [if_neg]
    rintro rfl
    exact hd ⟨y, rfl⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
