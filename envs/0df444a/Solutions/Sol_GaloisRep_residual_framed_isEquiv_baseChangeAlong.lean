-- Prove2me | solution 1 for GaloisRep.residual_framed_isEquiv_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6ea01bd5-d757-5d6b-ab76-4a2cfe7e5d19

import Mathlib
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_residual_framed_isEquiv_baseChangeAlong

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat

private lemma equiv_toLin_comm {S : Type} [CommRing S] {V₁ V₂ : Type}
    [AddCommGroup V₁] [Module S V₁] [AddCommGroup V₂] [Module S V₂]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (c₁ : Module.Basis ι S V₁) (c₂ : Module.Basis ι S V₂) (N : Matrix ι ι S) (x : V₁) :
    (c₁.equiv c₂ (Equiv.refl ι)) (Matrix.toLin c₁ c₁ N x)
      = Matrix.toLin c₂ c₂ N ((c₁.equiv c₂ (Equiv.refl ι)) x) := by
  have h : ((c₁.equiv c₂ (Equiv.refl ι)).toLinearMap.comp (Matrix.toLin c₁ c₁ N))
      = (Matrix.toLin c₂ c₂ N).comp (c₁.equiv c₂ (Equiv.refl ι)).toLinearMap := by
    apply c₁.ext
    intro j
    simp [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Matrix.toLin_self,
      map_sum, map_smul, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 4000000 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (IsLocalRing.ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    {R : Deformation.ProartinianCat 𝒪}
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).obj R)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom))) :
    ({ V := Fin 2 → R, finrank_eq := by simp,
       ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
       isAdicContinuous := hcont } : GaloisRepAdic R).residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R))) := by
  classical

  letI : Algebra (IsLocalRing.ResidueField 𝒪) (IsLocalRing.ResidueField R) :=
    (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)).toAlgebra

  have hρu' : @Eq ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ*
        GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
      ((Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).map
        (isTerminalResidueField.from R) ρu) ρ₀ := hρu

  have hkey : ∀ r : R, IsLocalRing.ResidueField.map (algebraMap 𝒪 R)
      ((isTerminalResidueField.from R).hom r) = IsLocalRing.residue R r := by
    intro r
    rw [ProartinianCat.to_residueField_apply (isTerminalResidueField.from R) r,
      IsLocalRing.ResidueField.map_residue, IsResidueAlgebra.residue_preimage]

  have hmat : ∀ σ, ((ρu σ).val).map (IsLocalRing.residue R)
      = (LinearMap.toMatrix b b (ρbar.ρ σ)).map
          (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)) := by
    intro σ
    have h5 : ((ρu σ).val).map (isTerminalResidueField.from R).hom.toRingHom
        = LinearMap.toMatrix b b (ρbar.ρ σ) := by
      have h4 := congrArg Units.val (DFunLike.congr_fun hρu' σ)
      rw [hρ₀ σ] at h4
      exact h4
    ext i j
    simp only [Matrix.map_apply]
    rw [← h5]
    simp only [Matrix.map_apply]
    exact (hkey ((ρu σ).val i j)).symm

  have hA : ∀ σ, LinearMap.toMatrix
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2)))
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2)))
      (((((Units.coeHom _).comp
          (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)) σ)).baseChange
        (IsLocalRing.ResidueField R))
      = (LinearMap.toMatrix b b (ρbar.ρ σ)).map
          (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)) := by
    intro σ
    rw [LinearMap.toMatrix_baseChange, ← hmat σ, IsLocalRing.ResidueField.algebraMap_eq]
    congr 1
    ext i j
    simp [Units.coeHom_apply]

  have hB : ∀ σ, LinearMap.toMatrix
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b)
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b)
      ((ρbar.ρ σ).baseChange (IsLocalRing.ResidueField R))
      = (LinearMap.toMatrix b b (ρbar.ρ σ)).map
          (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)) := by
    intro σ
    rw [LinearMap.toMatrix_baseChange]
    rfl

  refine ⟨⟨(Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2))).equiv
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b) (Equiv.refl _), ?_⟩⟩
  intro σ x
  show (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2))).equiv
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b) (Equiv.refl _)
      ((((((Units.coeHom _).comp
          (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)) σ)).baseChange
        (IsLocalRing.ResidueField R)) x)
    = ((ρbar.ρ σ).baseChange (IsLocalRing.ResidueField R))
      ((Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2))).equiv
        (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b) (Equiv.refl _) x)
  have e1 : (((((Units.coeHom _).comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)) σ)).baseChange
        (IsLocalRing.ResidueField R))
      = Matrix.toLin
          (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2)))
          (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) (Pi.basisFun R (Fin 2)))
          ((LinearMap.toMatrix b b (ρbar.ρ σ)).map
            (IsLocalRing.ResidueField.map (algebraMap 𝒪 R))) := by
    rw [← hA σ, Matrix.toLin_toMatrix]
  have e2 : ((ρbar.ρ σ).baseChange (IsLocalRing.ResidueField R))
      = Matrix.toLin
          (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b)
          (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b)
          ((LinearMap.toMatrix b b (ρbar.ρ σ)).map
            (IsLocalRing.ResidueField.map (algebraMap 𝒪 R))) := by
    rw [← hB σ, Matrix.toLin_toMatrix]
  rw [e1, e2]
  exact equiv_toLin_comm _ _ _ x

#print axioms solution

end S_GaloisRep_residual_framed_isEquiv_baseChangeAlong
end P2MW
export P2MW.S_GaloisRep_residual_framed_isEquiv_baseChangeAlong (solution)
