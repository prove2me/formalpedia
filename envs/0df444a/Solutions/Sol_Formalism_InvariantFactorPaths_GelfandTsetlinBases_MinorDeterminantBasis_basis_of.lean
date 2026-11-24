-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.basis_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:47.803878+00:00
-- url     : https://prove2.me/submissions/2840a839-af4e-486e-b9cf-82d96a27194d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_det_unit
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
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x))
    (R : Type) [CommRing R] :
    LinearIndependent R (fun x => MvPolynomial.map (Int.castRingHom R) (F x)) ∧
    Submodule.span R (Set.range fun x => MvPolynomial.map (Int.castRingHom R) (F x)) =
      Submodule.span R (Set.range fun y => monomial (m y) (1 : R)) := by
  classical
  set M := (cmat m F).map (Int.castRingHom R) with hM
  have hdet : IsUnit M.det := by
    have h1 := (det_unit m hm F hF hp).map (Int.castRingHom R)
    rw [RingHom.map_det] at h1
    exact h1
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have he : LinearIndependent R fun y => (monomial (m y) (1 : R) : MvPolynomial σ R) := by
    have h1 := (MvPolynomial.basisMonomials σ R).linearIndependent.comp m hm
    simpa [Function.comp_def, MvPolynomial.coe_basisMonomials] using h1
  have hexp : ∀ x, MvPolynomial.map (Int.castRingHom R) (F x) =
      ∑ y, M x y • (monomial (m y) (1 : R) : MvPolynomial σ R) := expand m hm F hF R
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp he _ hg
    have hv : Matrix.vecMul g M = 0 := funext fun y => by
      simpa [Matrix.vecMul, dotProduct] using h0 y
    have h2 := congrArg (fun v => Matrix.vecMul v M⁻¹) hv
    simp only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
    exact congrFun h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only
      rw [hexp]
      exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have key : ∑ x, M⁻¹ y x • MvPolynomial.map (Int.castRingHom R) (F x) =
          (monomial (m y) (1 : R) : MvPolynomial σ R) := by
        simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul]
        have h1 : ∀ z, ∑ x, M⁻¹ y x * M x z = (1 : Matrix X X R) y z := fun z => by
          rw [← hNM, Matrix.mul_apply]
        simp only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      dsimp only
      rw [← key]
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
