-- Prove2me | solution 1 for GaloisRep.DeformationRingData.exists_algHom_comp_eq_of_isOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed074668-d84c-5849-aed6-fe200beb5cd9

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType

set_option autoImplicit false

open GaloisRep
open scoped TensorProduct

namespace WCOTXprime

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem cancel_naturality (φ : V →ₗ[R] W) (x : T ⊗[S] (S ⊗[R] V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W ((φ.baseChange S).baseChange T x) =
      φ.baseChange T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality

variable {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

noncomputable def bcComp (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f)
    (g : B →+* C) (hg : IsLocalHom g) (hgf : IsLocalHom (g.comp f)) :
    GaloisRepAdic.Equiv ((ρ.baseChangeAlong f hf).baseChangeAlong g hg)
      (ρ.baseChangeAlong (g.comp f) hgf) :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
          ((((ρ.ρ σ).baseChange B).baseChange C) x) =
        ((ρ.ρ σ).baseChange C) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

theorem isUnramifiedAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (hur : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by
  obtain ⟨e⟩ := h
  intro P hP τ hτ
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  rw [← e.map_apply, hur P hP τ hτ, Module.End.one_apply, Module.End.one_apply]

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

theorem isEquiv_baseChangeAlong_comp
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪)) :
    (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsEquiv
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) := by
  obtain ⟨e⟩ := hθρ
  have hcomp : ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) = (x₀.comp θ : D'.R →+* 𝒪) :=
    RingHom.ext fun _ => rfl
  have hgf : IsLocalHom ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) := by rw [hcomp]; exact hx'
  have h1 : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsEquiv
      (D'.ρ.baseChangeAlong ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) hgf) := by
    have key : ∀ (f g : D'.R →+* 𝒪) (hf : IsLocalHom f) (hg : IsLocalHom g), f = g →
        (D'.ρ.baseChangeAlong f hf).IsEquiv (D'.ρ.baseChangeAlong g hg) := by
      intro f g hf hg hfg
      subst hfg
      exact ⟨GaloisRepAdic.Equiv.refl _⟩
    exact key _ _ hx' hgf hcomp.symm
  obtain ⟨e1⟩ := h1
  exact ⟨e1.trans ((bcComp D'.ρ (θ : D'.R →+* D₀.R) hθ (x₀ : D₀.R →+* 𝒪) hx₀ hgf).symm.trans
    (e.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀))⟩

theorem forall_inertia_apply_eq_one_comp
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪)) {q : ℕ}
    (hur : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsUnramifiedAt q) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').ρ τ = 1 :=
  isUnramifiedAt_of_isEquiv
    ⟨(Classical.choice (isEquiv_baseChangeAlong_comp D₀ D' θ hθ hθρ x₀ hx₀ hx')).symm⟩ hur

end WCOTXprime

namespace WCOTUniv

open GaloisRep WCOTXprime IsLocalRing
open scoped TensorProduct

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem cancel_symm_naturality (φ : V →ₗ[R] W) (y : T ⊗[R] V) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W).symm (φ.baseChange T y) =
      (φ.baseChange S).baseChange T
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cancel_naturality, LinearEquiv.apply_symm_apply]

end Naturality

section Adic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

noncomputable def residualBC (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f) :
    ResidualGaloisRep.Equiv (ρ.baseChangeAlong f hf).residual
      (ρ.residual.baseChangeAlong (@ResidueField.map A B _ _ _ _ f hf)) :=
  haveI := hf
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  letI : Module (ResidueField A) (ResidueField B) := Algebra.toModule
  haveI : IsScalarTower A (ResidueField A) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
          ρ.V).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
          (ResidueField B) ρ.V).symm
    map_apply := fun σ x => by
      change ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V ((((ρ.ρ σ).baseChange B).baseChange (ResidueField B)) x))) =
        ((ρ.ρ σ).baseChange (ResidueField A)).baseChange (ResidueField B)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V x))
      exact (congrArg ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm) (cancel_naturality (ρ.ρ σ) x)).trans
        (cancel_symm_naturality (ρ.ρ σ) _) }

end Adic

section Residual

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']

noncomputable def rbcComp (ρ : ResidualGaloisRep k) (f : k →+* k') (g : k' →+* k'') :
    ResidualGaloisRep.Equiv ((ρ.baseChangeAlong f).baseChangeAlong g)
      (ρ.baseChangeAlong (g.comp f)) :=
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k' k'' := g.toAlgebra
  letI : Algebra k k'' := (g.comp f).toAlgebra
  haveI : IsScalarTower k k' k'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
          ((((ρ.ρ σ).baseChange k').baseChange k'') x) =
        ((ρ.ρ σ).baseChange k'') (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

theorem risEquiv_congr (ρ : ResidualGaloisRep k) {f g : k →+* k'} (hfg : ∀ x, f x = g x) :
    (ρ.baseChangeAlong f).IsEquiv (ρ.baseChangeAlong g) := by
  obtain rfl : f = g := RingHom.ext hfg
  exact ⟨ResidualGaloisRep.Equiv.refl _⟩

theorem risEquiv_trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (h₁ : ρ₁.IsEquiv ρ₂) (h₂ : ρ₂.IsEquiv ρ₃) :
    ρ₁.IsEquiv ρ₃ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

end Residual

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟 𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

theorem residual_isEquiv_baseChangeAlong (D : DeformationRingData 𝒪 ρbar 𝒟)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)) :
    (D.ρ.baseChangeAlong (f : D.R →+* A) hf).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 A))) := by
  haveI := hf
  refine risEquiv_trans ⟨residualBC D.ρ (f : D.R →+* A) hf⟩ ?_
  obtain ⟨e⟩ := D.residual_isEquiv
  refine risEquiv_trans ⟨e.baseChangeAlong (ResidueField.map (f : D.R →+* A))⟩ ?_
  refine risEquiv_trans ⟨rbcComp ρbar _ _⟩ (risEquiv_congr ρbar fun y => ?_)
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  rw [RingHom.comp_apply, ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue A) (f.commutes r)

theorem algHom_eq_of_isEquiv (D : DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (f g : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)) (hg : IsLocalHom (g : D.R →+* A))
    (h𝒟 : 𝒟 (D.ρ.baseChangeAlong (f : D.R →+* A) hf))
    (hfg : (D.ρ.baseChangeAlong (f : D.R →+* A) hf).IsEquiv (D.ρ.baseChangeAlong (g : D.R →+* A) hg)) :
    f = g := by
  have hu := D.universal A hres _ h𝒟 (residual_isEquiv_baseChangeAlong D f hf)
  obtain ⟨egf⟩ := hfg
  exact hu.unique ⟨hf, ⟨GaloisRepAdic.Equiv.refl _⟩⟩ ⟨hg, ⟨egf.symm⟩⟩

theorem exists_algHom_comp_eq
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (xφ : D'.R →ₐ[𝒪] A) (hxφ : IsLocalHom (xφ : D'.R →+* A))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ)) :
    ∃ ψ : D₀.R →ₐ[𝒪] A, IsLocalHom (ψ : D₀.R →+* A) ∧ ψ.comp θ = xφ := by
  obtain ⟨ψ, ⟨hψ, hequiv⟩, -⟩ := D₀.universal A hres _ h𝒟₀ (residual_isEquiv_baseChangeAlong D' xφ hxφ)
  refine ⟨ψ, hψ, ?_⟩
  have hcomp : ((ψ : D₀.R →+* A).comp (θ : D'.R →+* D₀.R)) = (ψ.comp θ : D'.R →+* A) :=
    RingHom.ext fun _ => rfl
  haveI := hθ; haveI := hψ
  have hg : IsLocalHom (ψ.comp θ : D'.R →+* A) := by
    rw [← hcomp]; exact RingHom.isLocalHom_comp _ _
  have hgf : IsLocalHom ((ψ : D₀.R →+* A).comp (θ : D'.R →+* D₀.R)) := by rw [hcomp]; exact hg

  have key : ∀ (f g : D'.R →+* A) (hf : IsLocalHom f) (hg : IsLocalHom g), f = g →
      (D'.ρ.baseChangeAlong f hf).IsEquiv (D'.ρ.baseChangeAlong g hg) := by
    intro f g hf hg hfg; subst hfg; exact ⟨GaloisRepAdic.Equiv.refl _⟩
  obtain ⟨e0⟩ := key _ _ hg hgf hcomp.symm
  obtain ⟨e1⟩ := hθρ
  obtain ⟨e2⟩ := hequiv
  have hiso : (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ).IsEquiv
      (D'.ρ.baseChangeAlong (ψ.comp θ : D'.R →+* A) hg) :=
    ⟨(e0.trans ((bcComp D'.ρ (θ : D'.R →+* D₀.R) hθ (ψ : D₀.R →+* A) hψ hgf).symm.trans
      ((e1.baseChangeAlong (ψ : D₀.R →+* A) hψ).trans e2))).symm⟩
  exact (algHom_eq_of_isEquiv D' A hres xφ (ψ.comp θ) hxφ hg h𝒟' hiso).symm

end WCOTUniv

open GaloisRep

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (xφ : D'.R →ₐ[𝒪] A) (hxφ : IsLocalHom (xφ : D'.R →+* A))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ)) :
    ∃ ψ : D₀.R →ₐ[𝒪] A, IsLocalHom (ψ : D₀.R →+* A) ∧ ψ.comp θ = xφ := by
  exact WCOTUniv.exists_algHom_comp_eq D₀ D' θ hθ hθρ A hres xφ hxφ h𝒟' h𝒟₀

end S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType (solution)
