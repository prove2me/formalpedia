-- Prove2me | solution 1 for GaloisRep.exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2db1e1aa-fb90-5aec-a7c0-bb3bd9313eed

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace GaloisRep
namespace ConjOfCharpolyAux

noncomputable def bundle {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ) : ResidualGaloisRep F where
  V := Fin 2 → F
  finrank_eq := Module.finrank_fin_fun F
  ρ := { toFun := fun σ => Matrix.toLin' (ρ σ).val
         map_one' := by rw [map_one, Units.val_one, Matrix.toLin'_one]; rfl
         map_mul' := fun σ τ => by rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl }
  factorsThroughFiniteLevel := by
    obtain ⟨L, hL, h⟩ := hfin
    refine ⟨L, hL, fun σ hσ => ?_⟩
    show Matrix.toLin' (ρ σ).val = 1
    rw [h σ hσ, Units.val_one, Matrix.toLin'_one]
    rfl

theorem bundle_ρ_apply {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (bundle ρ hfin).ρ σ = Matrix.toLin' (ρ σ).val := rfl

theorem charpoly_bundle {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((bundle ρ hfin).ρ σ).charpoly = (ρ σ).val.charpoly := by
  rw [bundle_ρ_apply]
  change LinearMap.charpoly (Matrix.toLin' (ρ σ).val : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) = _
  rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' (ρ σ).val) (Pi.basisFun F (Fin 2)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem isAbsolutelyIrreducible_bundle {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hρabs : ∀ u : Fin 2 → AlgebraicClosure F, u ≠ 0 →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        Matrix.mulVec ((ρ σ).val.map (algebraMap F (AlgebraicClosure F))) u ∉ (AlgebraicClosure F) ∙ u) :
    (bundle ρ hfin).IsAbsolutelyIrreducible := by
  classical
  set K := AlgebraicClosure F
  intro W hW
  by_contra hne
  push Not at hne
  obtain ⟨hbot, htop⟩ := hne

  let b : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
  let bK : Module.Basis (Fin 2) K (K ⊗[F] (Fin 2 → F)) := Algebra.TensorProduct.basis K b
  haveI : FiniteDimensional K (K ⊗[F] (Fin 2 → F)) := Module.Finite.of_basis bK
  have hdim : Module.finrank K (K ⊗[F] (Fin 2 → F)) = 2 := by
    rw [Module.finrank_eq_card_basis bK, Fintype.card_fin]

  have hW1 : Module.finrank K W = 1 := by
    have hlt := Submodule.finrank_lt htop
    have hne0 : Module.finrank K W ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
    change Module.finrank K W < Module.finrank K (K ⊗[F] (Fin 2 → F)) at hlt
    rw [hdim] at hlt
    omega
  obtain ⟨⟨w, hwW⟩, hw0, hgen⟩ := finrank_eq_one_iff'.mp hW1
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  set u : Fin 2 → K := ⇑(bK.repr w) with hudef
  have hu0 : u ≠ 0 := by
    intro h0
    apply hw0'
    have h1 : bK.repr w = 0 := Finsupp.ext fun i => congr_fun h0 i
    exact bK.repr.map_eq_zero_iff.mp h1
  obtain ⟨σ, hσ⟩ := hρabs u hu0
  apply hσ

  have hmem : ((bundle ρ hfin).ρ σ).baseChange K w ∈ W := hW σ w hwW
  obtain ⟨c, hc⟩ := hgen ⟨_, hmem⟩
  have hc' : ((bundle ρ hfin).ρ σ).baseChange K w = c • w := by
    have := congrArg Subtype.val hc
    simpa using this.symm

  have hmat : LinearMap.toMatrix bK bK (((bundle ρ hfin).ρ σ).baseChange K) =
      (ρ σ).val.map (algebraMap F K) := by
    rw [bundle_ρ_apply]
    change LinearMap.toMatrix (Algebra.TensorProduct.basis K b) (Algebra.TensorProduct.basis K b)
      (LinearMap.baseChange K (Matrix.toLin' (ρ σ).val)) = _
    rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hcoord : ((ρ σ).val.map (algebraMap F K)).mulVec u = c • u := by
    have h := LinearMap.toMatrix_mulVec_repr bK bK (((bundle ρ hfin).ρ σ).baseChange K) w
    rw [hmat] at h
    refine h.trans ?_
    change ⇑(bK.repr (((bundle ρ hfin).ρ σ).baseChange K w)) = c • ⇑(bK.repr w)
    rw [hc']
    exact (congrArg DFunLike.coe (bK.repr.map_smul c w)).trans (Finsupp.coe_smul _ _)
  rw [hcoord]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

end GaloisRep.ConjOfCharpolyAux

open GaloisRep.ConjOfCharpolyAux in

theorem solution
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    {F : Type} [Field F]
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ) (hfin' : GaloisFactorsThroughFiniteLevel ρ')
    (hρabs : ∀ u : Fin 2 → AlgebraicClosure F, u ≠ 0 →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        Matrix.mulVec ((ρ σ).val.map (algebraMap F (AlgebraicClosure F))) u ∉ (AlgebraicClosure F) ∙ u)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ τ).val.charpoly = (ρ' τ).val.charpoly) :
    ∃ g : GL (Fin 2) F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ' σ).val = g.val * (ρ σ).val * (g⁻¹).val := by
  classical
  set ρ₁ := bundle ρ hfin with hρ₁
  set ρ₂ := bundle ρ' hfin' with hρ₂
  have hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
    refine ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq hFD ρ₁ ρ₂ S ?_
    intro ℓ hℓ hℓS A τ hA hτ
    rw [hρ₁, hρ₂, charpoly_bundle, charpoly_bundle]
    exact hfrob ℓ hℓ hℓS A τ hA hτ
  have h₁ : ρ₁.IsAbsolutelyIrreducible := isAbsolutelyIrreducible_bundle ρ hfin hρabs
  have h₂ : ρ₂.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₁ ρ₂ h₁ hcp
  obtain ⟨E⟩ := ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₁ ρ₂ h₁ h₂ hcp

  let T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) := E.toLinearEquiv
  have hT : ∀ σ x, T (Matrix.toLin' (ρ σ).val x) = Matrix.toLin' (ρ' σ).val (T x) := E.map_apply
  set g : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix' T.toLinearMap with hg
  set gi : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix' T.symm.toLinearMap with hgi
  have hggi : g * gi = 1 := by
    rw [hg, hgi, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hgig : gi * g = 1 := by
    rw [hg, hgi, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hcomm : ∀ σ, g * (ρ σ).val = (ρ' σ).val * g := by
    intro σ
    have hlin : T.toLinearMap ∘ₗ Matrix.toLin' (ρ σ).val = Matrix.toLin' (ρ' σ).val ∘ₗ T.toLinearMap := by
      apply LinearMap.ext
      intro x
      exact hT σ x
    have h := congrArg LinearMap.toMatrix' hlin
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin', ← hg] at h
  refine ⟨⟨g, gi, hggi, hgig⟩, fun σ => ?_⟩
  show (ρ' σ).val = g * (ρ σ).val * gi
  rw [hcomm σ, Matrix.mul_assoc, hggi, Matrix.mul_one]

end S_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
end P2MW
export P2MW.S_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible (solution)
