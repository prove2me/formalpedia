-- Prove2me | solution 1 for GaloisRepAdic.galoisActionIsAdicContinuous_toLin_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4fa2ab1c-5681-5173-8731-aa6279d25c13

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_Deformations_LiftFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous

set_option autoImplicit false

open IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (A : Deformation.ProartinianCat 𝒪) [IsLocalRing.IsAdicTopology A]
    (ρ' : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj A) :
    GaloisActionIsAdicContinuous A
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ'.toMonoidHom)) := by

  let ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) A := ρ'
  intro n

  set I : Ideal A := maximalIdeal A ^ n with hIdef
  have hI : IsOpen (I : Set A) := IsLocalRing.isOpen_maximalIdeal_pow'' A n

  let U : Set (Matrix (Fin 2) (Fin 2) A) := {M | ∀ i j, M i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ I}
  have hU : IsOpen U := by
    have hUeq : U = ⋂ i, ⋂ j,
        (fun M : Matrix (Fin 2) (Fin 2) A => M i j - (1 : Matrix (Fin 2) (Fin 2) A) i j) ⁻¹' (I : Set A) := by
      ext M
      simp only [U, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [hUeq]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hI.preimage ?_
    exact (continuous_apply_apply i j).sub continuous_const

  have hcont : Continuous fun σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =>
      ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) :=
    Units.continuous_val.comp (map_continuous ρ)
  have hmem : (fun σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =>
      ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) ⁻¹' U ∈
      nhds (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
    refine (hU.preimage hcont).mem_nhds ?_
    simp only [Set.mem_preimage, U, Set.mem_setOf_eq, map_one, Units.val_one, sub_self, ρ]
    exact fun _ _ => I.zero_mem

  obtain ⟨E, hE, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
  refine ⟨E, hE, fun σ hσ v => ?_⟩
  have hσmem : σ ∈ (E.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    exact hσ
  have hρσ : ∀ i j, ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j -
      (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ I := hEsub hσmem

  set M : Matrix (Fin 2) (Fin 2) A := ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) with hM
  have hact : ((Units.coeHom _).comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ'.toMonoidHom)) σ v = M.mulVec v := by
    show ((Matrix.GeneralLinearGroup.toLin (ρ σ) : LinearMap.GeneralLinearGroup A (Fin 2 → A)) :
      (Fin 2 → A) →ₗ[A] (Fin 2 → A)) v = _
    rw [Matrix.GeneralLinearGroup.coe_toLin]
    rfl
  rw [hact, show M.mulVec v - v = (M - 1).mulVec v by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]

  have hcoord : ∀ i, (M - 1).mulVec v i ∈ I := by
    intro i
    rw [Matrix.mulVec, dotProduct]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (by simpa [Matrix.sub_apply] using hρσ i j)
  have hdecomp : (M - 1).mulVec v = ∑ i, ((M - 1).mulVec v i) • (Pi.single i (1 : A) : Fin 2 → A) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdecomp]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) Submodule.mem_top

end S_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous
end P2MW
export P2MW.S_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous (solution)
