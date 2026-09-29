-- Prove2me | solution 1 for GaloisRep.exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b6de32a1-5e43-50c1-beef-5efe30f3e4c5

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import Theorems.Thm_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous
import Theorems.Thm_Deformation_isLocalProartinianAlgebra_of_isAdicComplete
import Theorems.Thm_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous
import Definitions.Def_Deformations_ProartinianCompact
import Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy

set_option autoImplicit false
set_option maxHeartbeats 0

open CategoryTheory IsLocalRing Deformation Deformation.ProartinianCat

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxC9a
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

abbrev StdCont (X : ProartinianCat 𝒪) (τ : Γℚ →ₜ* GL (Fin 2) X) : Prop :=
  GaloisActionIsAdicContinuous X
    ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom))

noncomputable def mkStd (X : ProartinianCat 𝒪) (τ : Γℚ →ₜ* GL (Fin 2) X) (hc : StdCont X τ) :
    GaloisRepAdic X where
  V := Fin 2 → X
  finrank_eq := by simp
  ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)
  isAdicContinuous := hc

lemma mkStd_ρ_apply (X : ProartinianCat 𝒪) (τ : Γℚ →ₜ* GL (Fin 2) X) (hc : StdCont X τ) (σ : Γℚ) (v : Fin 2 → X) :
    (mkStd X τ hc).ρ σ v = ((τ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X).mulVec v := by
  show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup X (Fin 2 → X)) :
    (Fin 2 → X) →ₗ[X] (Fin 2 → X)) v = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl

theorem isEquiv_baseChangeAlong_mkStd (X Y : ProartinianCat 𝒪) (f : X ⟶ Y) (hf : IsLocalHom f.hom.toRingHom)
    (τ : Γℚ →ₜ* GL (Fin 2) X) (hcX : StdCont X τ) (hcY : StdCont Y (mapRepn (Fin 2) Γℚ 𝒪 f τ)) :
    ((mkStd X τ hcX).baseChangeAlong f.hom.toRingHom hf).IsEquiv
      (mkStd Y (mapRepn (Fin 2) Γℚ 𝒪 f τ) hcY) := by
  letI : Algebra X Y := f.hom.toRingHom.toAlgebra
  refine ⟨{ toLinearEquiv := TensorProduct.piScalarRight X Y Y (Fin 2), map_apply := fun σ => ?_ }⟩
  change ∀ x : TensorProduct X Y (Fin 2 → X),
    (TensorProduct.piScalarRight X Y Y (Fin 2))
        (((Matrix.mulVecLin ((τ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X)).baseChange Y) x) =
      ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) Y) :
          Matrix (Fin 2) (Fin 2) Y).mulVec ((TensorProduct.piScalarRight X Y Y (Fin 2)) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, Matrix.mulVec_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mulVec_add]
  | tmul n v =>
    rw [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
    funext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
    have hmap : ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y)
        = ((τ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X).map f.hom.toRingHom := by
      rw [Matrix.GeneralLinearGroup.map, Units.coe_map]; rfl
    simp only [hmap, Matrix.map_apply, Matrix.mulVec, dotProduct, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      map_sum, map_mul, Finset.sum_mul, mul_assoc]

theorem isEquiv_symm {B : Type} [CommRing B] [IsLocalRing B] {ρ ρ' : GaloisRepAdic B} (h : ρ.IsEquiv ρ') :
    ρ'.IsEquiv ρ := ⟨h.some.symm⟩
theorem isEquiv_trans {B : Type} [CommRing B] [IsLocalRing B] {ρ ρ' ρ'' : GaloisRepAdic B}
    (h : ρ.IsEquiv ρ') (h' : ρ'.IsEquiv ρ'') : ρ.IsEquiv ρ'' := ⟨h.some.trans h'.some⟩
theorem isEquiv_baseChangeAlong_congr {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    {φ ψ : A →+* B} (h : φ = ψ) (hφ : IsLocalHom φ) (hψ : IsLocalHom ψ) (ρ : GaloisRepAdic A) :
    (ρ.baseChangeAlong φ hφ).IsEquiv (ρ.baseChangeAlong ψ hψ) := by
  subst h; exact ⟨GaloisRepAdic.Equiv.refl _⟩

theorem exists_conj_of_isEquiv_mkStd (Y : ProartinianCat 𝒪) (τ₁ τ₂ : Γℚ →ₜ* GL (Fin 2) Y)
    (hc₁ : StdCont Y τ₁) (hc₂ : StdCont Y τ₂) (h : (mkStd Y τ₁ hc₁).IsEquiv (mkStd Y τ₂ hc₂)) :
    ∃ g : GL (Fin 2) Y, ∀ σ, g * τ₁ σ * g⁻¹ = τ₂ σ := by
  obtain ⟨e⟩ := h
  let L : (Fin 2 → Y) ≃ₗ[Y] (Fin 2 → Y) := e.toLinearEquiv
  have h1 : LinearMap.toMatrix' L.toLinearMap * LinearMap.toMatrix' L.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun v => L.apply_symm_apply v)
  have h2 : LinearMap.toMatrix' L.symm.toLinearMap * LinearMap.toMatrix' L.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun v => L.symm_apply_apply v)
  let g : GL (Fin 2) Y := ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap, h1, h2⟩
  have hg : ∀ w, (g : Matrix (Fin 2) (Fin 2) Y).mulVec w = L w := fun w => LinearMap.toMatrix'_mulVec _ _
  refine ⟨g, fun σ => ?_⟩
  have key : (g : Matrix (Fin 2) (Fin 2) Y) * ((τ₁ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) =
      ((τ₂ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) * (g : Matrix (Fin 2) (Fin 2) Y) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hg, hg]
    have := e.map_apply σ v
    rw [mkStd_ρ_apply, mkStd_ρ_apply] at this
    exact this
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext key

open Deformation Deformation.ProartinianCat TensorProduct

theorem discreteTopology_of_isArtinianRing (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    DiscreteTopology B := by

  have hne : {I : Ideal B | IsOpen (I : Set B)}.Nonempty := ⟨⊤, isOpen_univ⟩
  obtain ⟨I₀, hI₀open, hI₀min⟩ :=
    (IsArtinian.set_has_minimal (R := B) (M := B) {I : Ideal B | IsOpen (I : Set B)} hne)

  have hle : ∀ J : Ideal B, IsOpen (J : Set B) → I₀ ≤ J := by
    intro J hJ
    have hinf : IsOpen ((I₀ ⊓ J : Ideal B) : Set B) := by
      have : ((I₀ ⊓ J : Ideal B) : Set B) = (I₀ : Set B) ∩ (J : Set B) := rfl
      rw [this]; exact hI₀open.inter hJ
    have := hI₀min (I₀ ⊓ J) hinf

    have heq : I₀ ⊓ J = I₀ := by
      by_contra hne'
      exact this (lt_of_le_of_ne inf_le_left hne')
    exact heq ▸ inf_le_right

  have hbot : I₀ = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    by_contra hx0

    have hmem : ({x}ᶜ : Set B) ∈ nhds (0 : B) :=
      isOpen_compl_singleton.mem_nhds (fun h => hx0 (Set.mem_singleton_iff.mp h).symm)
    obtain ⟨J, hJopen, hJsub⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp hmem
    exact hJsub (hle J hJopen hx) rfl

  rw [hbot] at hI₀open
  have h0 : IsOpen ({0} : Set B) := by simpa using hI₀open
  exact discreteTopology_iff_isOpen_singleton_zero.mpr h0 |> fun h => h

theorem isArtinianTestAlgebra_obj (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    GaloisRep.IsArtinianTestAlgebra 𝒪 B where
  isLocalHom := inferInstance
  residue_surjective := by
    have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (B : Type)
    rwa [IsScalarTower.algebraMap_eq 𝒪 B (ResidueField B), ResidueField.algebraMap_eq, RingHom.coe_comp] at h
  isArtinian := inferInstance

theorem isEquiv_baseChangeAlong_baseChangeAlong {A B C : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ψ : B →+* C) (hψ : IsLocalHom ψ) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong φ hφ).baseChangeAlong ψ hψ).IsEquiv
      (ρ.baseChangeAlong (ψ.comp φ) (RingHom.isLocalHom_comp ψ φ)) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B C := ψ.toAlgebra
  letI : Algebra A C := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V,
            map_apply := fun σ => ?_ }⟩
  change ∀ x : C ⊗[B] (B ⊗[A] ρ.V),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V) (((ρ.ρ σ).baseChange B).baseChange C x) =
      (ρ.ρ σ).baseChange C ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero, map_zero, map_zero]
    | add y₁ y₂ h₁ h₂ => rw [tmul_add, map_add, map_add, h₁, h₂, map_add, map_add]
    | tmul b v =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]

theorem finite_of_isArtinianRing' [Finite (ResidueField 𝒪)] (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    Finite B := by
  haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B
  haveI : Finite (B ⧸ (⊥ : Ideal B)) := IsProartinian.finite_quotient_of_isOpen (R := B) ⊥ (isOpen_discrete _)
  exact Finite.of_equiv _ (RingEquiv.quotientBot B).toEquiv

theorem isLocalHom_of_algHom_of_residue_surjective'
    {R A : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    (hA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (φ : R →ₐ[𝒪] A) : IsLocalHom (φ : R →+* A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr hxu
  obtain ⟨o, ho⟩ := hA (IsLocalRing.residue A (φ x))
  simp only [Function.comp_apply] at ho
  have hou : IsUnit o := by
    by_contra hou
    have hom : algebraMap 𝒪 A o ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hou ((isUnit_map_iff (algebraMap 𝒪 A) o).mp h)
    have h0 : IsLocalRing.residue A (φ x) = 0 := by
      rw [← ho, IsLocalRing.residue_eq_zero_iff]
      exact hom
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
    exact h0 hx
  have hker : x - algebraMap 𝒪 R o ∈ IsLocalRing.maximalIdeal R := by
    have hmem : x - algebraMap 𝒪 R o ∈ RingHom.ker ((IsLocalRing.residue A).comp (φ : R →+* A)) := by
      rw [RingHom.mem_ker, RingHom.comp_apply, map_sub, RingHom.coe_coe, AlgHom.commutes, map_sub, ho, sub_self]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) hmem
  have : algebraMap 𝒪 R o ∈ IsLocalRing.maximalIdeal R := by
    have h := sub_mem hxm hker
    rwa [sub_sub_cancel] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp this (hou.map _)

theorem stdCont_of_isArtinianRing (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B) :
    StdCont B τ := by
  haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B
  intro n
  have hcont : Continuous fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) :=
    Units.continuous_val.comp (map_continuous τ)
  have hmem : (fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) ⁻¹' {1} ∈ nhds (1 : Γℚ) := by
    refine ((isOpen_discrete _).preimage hcont).mem_nhds ?_
    simp
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
  refine ⟨L, hL, fun σ hσ v => ?_⟩
  have hσmem : σ ∈ (L.fixingSubgroup : Set Γℚ) := by
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]; exact hσ
  have h1 : ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) = 1 := hsub hσmem
  have hact : ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)) σ v =
      ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).mulVec v := by
    show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup B (Fin 2 → B)) :
      (Fin 2 → B) →ₗ[B] (Fin 2 → B)) v = _
    rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl
  rw [hact, h1, Matrix.one_mulVec, sub_self]
  exact Submodule.zero_mem _

theorem isEquiv_mkStd_of_conj (Y : ProartinianCat 𝒪) (τ₁ τ₂ : Γℚ →ₜ* GL (Fin 2) Y)
    (hc₁ : StdCont Y τ₁) (hc₂ : StdCont Y τ₂) (g : GL (Fin 2) Y) (hg : ∀ σ, g * τ₁ σ * g⁻¹ = τ₂ σ) :
    (mkStd Y τ₁ hc₁).IsEquiv (mkStd Y τ₂ hc₂) := by
  let L : (Fin 2 → Y) ≃ₗ[Y] (Fin 2 → Y) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Y (Fin 2 → Y)) (Matrix.GeneralLinearGroup.toLin g)
  have hgv : ∀ w : Fin 2 → Y, L w = (g : Matrix (Fin 2) (Fin 2) Y).mulVec w := by
    intro w
    show ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup Y (Fin 2 → Y)) :
      (Fin 2 → Y) →ₗ[Y] (Fin 2 → Y)) w = _
    rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl
  refine ⟨{ toLinearEquiv := L, map_apply := fun σ => ?_ }⟩
  change ∀ v : Fin 2 → Y, L ((mkStd Y τ₁ hc₁).ρ σ v) = (mkStd Y τ₂ hc₂).ρ σ (L v)
  intro v
  have hmat : (g : Matrix (Fin 2) (Fin 2) Y) * ((τ₁ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) =
      ((τ₂ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) * (g : Matrix (Fin 2) (Fin 2) Y) := by
    have h1 : g * τ₁ σ = τ₂ σ * g := by rw [← hg σ, inv_mul_cancel_right]
    have := congrArg (Units.val) h1
    rwa [Units.val_mul, Units.val_mul] at this
  rw [hgv, hgv, mkStd_ρ_apply, mkStd_ρ_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]

theorem exists_basis_tmul_eq {A : Type} [CommRing A] [IsLocalRing A] {V : Type} [AddCommGroup V] [Module A V]
    [Module.Free A V] [Module.Finite A V] (hrank : Module.finrank A V = 2)
    (bbar : Module.Basis (Fin 2) (ResidueField A) (TensorProduct A (ResidueField A) V)) :
    ∃ B : Module.Basis (Fin 2) A V, ∀ i, (1 : ResidueField A) ⊗ₜ[A] B i = bbar i := by
  classical
  have hsurj : Function.Surjective (TensorProduct.mk A (ResidueField A) V 1) :=
    TensorProduct.mk_surjective A V (ResidueField A) residue_surjective
  choose f hf using fun i => hsurj (bbar i)
  have hspan : Submodule.span A (Set.range f) = ⊤ := IsLocalRing.span_eq_top_of_tmul_eq_basis f bbar hf
  let e : V ≃ₗ[A] (Fin 2 → A) := (Module.finBasisOfFinrankEq A V hrank).equivFun
  have hTsurj : Function.Surjective (Fintype.linearCombination A f) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  have hinj : Function.Injective (Fintype.linearCombination A f) := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ Fintype.linearCombination A f)
      (e.surjective.comp hTsurj)
    intro x y hxy
    exact h (by simp only [LinearMap.comp_apply, hxy])
  have hli : LinearIndependent A f := linearIndependent_iff_injective_fintypeLinearCombination.mpr hinj
  refine ⟨Module.Basis.mk hli (by rw [hspan]), fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hf i

theorem toMatrix_map_map {R : Type} [CommRing R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (b : Module.Basis (Fin 2) R V) (e : V ≃ₗ[R] W) (T : Module.End R W) :
    LinearMap.toMatrix (b.map e) (b.map e) T = LinearMap.toMatrix b b (e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.map_apply]

end GaloisRep.SolAuxC9a

open GaloisRep.SolAuxC9a in
p2m_attr_erase "instance" "IsLocalRing.ResidueField.instAlgebra IsLocalRing.ResidueField.instModule in"
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    {R : Deformation.ProartinianCat 𝒪} [IsLocalRing.IsAdicTopology R]
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R)
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj R)
    (hρu' : (Quotient.mk'' ρu : (Deformation.repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj R) = (e.homEquiv (𝟙 R)).1)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)))
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hresA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hDA : 𝒟 ρA)
    (hresEq : ρA.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A)))) :
    ∃ φ : R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : R →+* A),
      (GaloisRepAdic.baseChangeAlong (φ : R →+* A) hφ
        { V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont }).IsEquiv ρA := by
  classical

  letI tA : TopologicalSpace A := (maximalIdeal A).adicTopology
  haveI iA : @IsLocalProartinianAlgebra 𝒪 _ A _ (maximalIdeal A).adicTopology _ :=
    Deformation.isLocalProartinianAlgebra_of_isAdicComplete 𝒪 A hresA
  let Aobj : ProartinianCat 𝒪 := ProartinianCat.of 𝒪 A
  haveI : IsLocalRing.IsAdicTopology (Aobj : Type) := ⟨rfl⟩
  let ρR : GaloisRepAdic R := mkStd R ρu hcont

  let kA := ResidueField A
  let ψ : ResidueField 𝒪 →+* kA := IsLocalRing.ResidueField.map (algebraMap 𝒪 A)
  letI algψ : Algebra (ResidueField 𝒪) kA := ψ.toAlgebra
  obtain ⟨E⟩ := hresEq

  let b' : Module.Basis (Fin 2) kA (TensorProduct (ResidueField 𝒪) kA ρbar.V) := Algebra.TensorProduct.basis kA b
  let bbar : Module.Basis (Fin 2) kA (TensorProduct A kA ρA.V) := b'.map E.toLinearEquiv.symm
  have hbbar : ∀ σ, LinearMap.toMatrix bbar bbar (ρA.residual.ρ σ) =
      (ρ₀ σ).val.map ψ := by
    intro σ
    rw [toMatrix_map_map]
    have hint : E.toLinearEquiv.symm.symm.toLinearMap ∘ₗ ρA.residual.ρ σ ∘ₗ E.toLinearEquiv.symm.toLinearMap =
        (ρbar.baseChangeAlong ψ).ρ σ := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_symm]
      rw [E.map_apply, LinearEquiv.apply_symm_apply]
    refine (congrArg (LinearMap.toMatrix b' b') hint).trans ?_

    have hbc : (ρbar.baseChangeAlong ψ).ρ σ = (ρbar.ρ σ).baseChange kA := rfl
    rw [hbc]
    show LinearMap.toMatrix (Algebra.TensorProduct.basis kA b) (Algebra.TensorProduct.basis kA b) _ = _
    rw [LinearMap.toMatrix_baseChange, ← hρ₀ σ]
    rfl
  obtain ⟨B, hB⟩ := exists_basis_tmul_eq (A := A) ρA.finrank_eq bbar

  have hBres : ∀ σ i j, residue A (LinearMap.toMatrix B B (ρA.ρ σ) i j) =
      ψ ((ρ₀ σ).val i j) := by
    intro σ i j
    have hbb : bbar = Algebra.TensorProduct.basis kA B := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      rw [Algebra.TensorProduct.basis_apply, hB]
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) kA => M i j) (hbbar σ)
    rw [hbb] at h1
    have h2 : LinearMap.toMatrix (Algebra.TensorProduct.basis kA B) (Algebra.TensorProduct.basis kA B) (ρA.residual.ρ σ) =
        (LinearMap.toMatrix B B (ρA.ρ σ)).map (algebraMap A kA) := by
      have : ρA.residual.ρ σ = (ρA.ρ σ).baseChange kA := rfl
      rw [this, LinearMap.toMatrix_baseChange]
    rw [h2, Matrix.map_apply, Matrix.map_apply, ResidueField.algebraMap_eq] at h1
    exact h1

  let τm : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) A :=
    (Units.map (LinearMap.toMatrixAlgEquiv B).toMonoidHom).comp ρA.ρ.toHomUnits
  have hτcont : Continuous τm :=
    GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous Aobj ρA B
  let τA : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) Aobj := ⟨τm, hτcont⟩
  have hτA : ∀ σ, ((τA σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = LinearMap.toMatrix B B (ρA.ρ σ) := fun σ => rfl

  have hτlift : mapRepn (Fin 2) _ 𝒪 (toResidueField Aobj) τA = ρ₀ := by
    apply ContinuousMonoidHom.ext
    intro σ
    rw [mapRepn_apply]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.map, Units.coe_map]
    ext i j
    show (toResidueField Aobj).hom (((τA σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j) = _
    rw [hτA]

    show (IsResidueAlgebra.algEquiv 𝒪 A).symm (algebraMap A kA (LinearMap.toMatrix B B (ρA.ρ σ) i j)) = _
    rw [ResidueField.algebraMap_eq, hBres, AlgEquiv.symm_apply_eq]
    rfl
  have hτmem : τA ∈ (liftFunctor (Fin 2) _ 𝒪 ρ₀).obj Aobj := by
    show (repnFunctor (Fin 2) _ 𝒪).map (isTerminalResidueField.from Aobj) τA ∈ ({ρ₀} : Set _)
    rw [Subsingleton.elim (isTerminalResidueField.from Aobj) (toResidueField Aobj)]
    exact hτlift

  have hcA : StdCont Aobj τA := GaloisRepAdic.galoisActionIsAdicContinuous_toLin_of_continuous Aobj τA
  have eA : ρA.IsEquiv (mkStd Aobj τA hcA) := by
    refine ⟨{ toLinearEquiv := B.equivFun, map_apply := fun σ x => ?_ }⟩
    rw [mkStd_ρ_apply, hτA]
    show (B.equivFun : ρA.V → (Fin 2 → A)) (ρA.ρ σ x) = _
    funext i
    simp only [Module.Basis.equivFun_apply]
    rw [← LinearMap.toMatrix_mulVec_repr B B (ρA.ρ σ) x]
    rfl

  have tA_loc : IsLocalHom (algebraMap 𝒪 A) := inferInstance
  have hDArt : ∀ ⦃B₀ : Type⦄ [CommRing B₀] [IsLocalRing B₀] [Algebra 𝒪 B₀], GaloisRep.IsArtinianTestAlgebra 𝒪 B₀ →
      ∀ (q : A →ₐ[𝒪] B₀) (hq : IsLocalHom (q : A →+* B₀)), Function.Surjective q →
        𝒟 (ρA.baseChangeAlong (q : A →+* B₀) hq) :=
    fun B₀ _ _ _ tB₀ q hq hqs => ((h𝒟.iff_forall_surjective tA_loc hresA ρA).mp hDA) tB₀ q hq hqs
  have hτcond : τA ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ Aobj := by
    refine ⟨hτmem, ?_⟩
    intro B' _ f ρB' bB' hbB'
    haveI : Finite B' := finite_of_isArtinianRing' (𝒪 := 𝒪) B'
    have tB' : GaloisRep.IsArtinianTestAlgebra 𝒪 B' := isArtinianTestAlgebra_obj (𝒪 := 𝒪) B'

    let S : Subalgebra 𝒪 B' := (f.hom : Aobj →ₐ[𝒪] B').range
    let q : A →ₐ[𝒪] S := (f.hom : Aobj →ₐ[𝒪] B').rangeRestrict
    have hqs : Function.Surjective q := (f.hom : Aobj →ₐ[𝒪] B').rangeRestrict_surjective
    haveI : IsLocalRing S := IsLocalRing.of_surjective' (q : A →+* S) hqs
    let ι : S →ₐ[𝒪] B' := S.val
    have hιinj : Function.Injective ι := Subtype.val_injective
    have hfac : (ι : S →+* B').comp (q : A →+* S) = f.hom.toRingHom := RingHom.ext fun _ => rfl

    haveI hfl : IsLocalHom f.hom := by
      have h := isLocalHom_of_isContinuous_of_isProartinian f.hom.toRingHom f.hom.cont
      exact ⟨fun a ha => h.1 a ha⟩
    have hι_unit : ∀ s : S, IsUnit s ↔ IsUnit (s : B') := by
      intro s
      constructor
      · exact fun h => h.map ι
      · intro h

        obtain ⟨a, rfl⟩ := hqs s
        by_cases ha : IsUnit a
        · exact ha.map q
        · exfalso
          have : ¬ IsUnit (f.hom a) := fun hu => ha ((isUnit_map_iff f.hom a).mp hu)
          exact this h
    have hqloc : IsLocalHom (q : A →+* S) := ⟨fun a ha => by
      have : IsUnit (f.hom a) := (hι_unit (q a)).mp ha
      exact (isUnit_map_iff f.hom a).mp this⟩
    have tS : GaloisRep.IsArtinianTestAlgebra 𝒪 S :=
      { isLocalHom := ⟨fun o ho => (isUnit_map_iff (algebraMap 𝒪 B') o).mp ((hι_unit _).mp ho)⟩
        residue_surjective := by
          intro y
          obtain ⟨s, rfl⟩ := residue_surjective y
          obtain ⟨a, rfl⟩ := hqs s
          obtain ⟨o, ho⟩ := hresA (residue A a)
          refine ⟨o, ?_⟩
          show residue S (algebraMap 𝒪 S o) = residue S (q a)
          have h1 : algebraMap 𝒪 S o = q (algebraMap 𝒪 A o) := (q.commutes o).symm
          rw [h1, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub]
          have h2 : algebraMap 𝒪 A o - a ∈ maximalIdeal A := by
            rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ho
          haveI := hqloc
          exact (mem_maximalIdeal _).mpr (map_nonunit (q : A →+* S) _ ((mem_maximalIdeal _).mp h2))
        isArtinian := by haveI : Finite S := inferInstance; infer_instance }
    have hιloc : IsLocalHom (ι : S →+* B') := ⟨fun s hs => (hι_unit s).mpr hs⟩
    have hfloc : IsLocalHom f.hom.toRingHom := hfac ▸ RingHom.isLocalHom_comp _ _

    have hDq : 𝒟 (ρA.baseChangeAlong (q : A →+* S) hqloc) := hDArt tS q hqloc hqs
    have hDι : 𝒟 ((ρA.baseChangeAlong (q : A →+* S) hqloc).baseChangeAlong (ι : S →+* B') hιloc) :=
      h𝒟.baseChangeAlong tS tB' ι hιloc hDq
    have e1 := isEquiv_baseChangeAlong_baseChangeAlong (q : A →+* S) hqloc (ι : S →+* B') hιloc ρA
    have e2 := isEquiv_baseChangeAlong_congr hfac (RingHom.isLocalHom_comp _ _) hfloc ρA
    have hDf : 𝒟 (ρA.baseChangeAlong f.hom.toRingHom hfloc) := h𝒟.of_isEquiv tB' (isEquiv_trans e1 e2) hDι

    have e3 : (ρA.baseChangeAlong f.hom.toRingHom hfloc).IsEquiv ((mkStd Aobj τA hcA).baseChangeAlong f.hom.toRingHom hfloc) :=
      ⟨GaloisRepAdic.Equiv.baseChangeAlong _ hfloc eA.some⟩
    have hcB' : StdCont B' (mapRepn (Fin 2) _ 𝒪 f τA) := stdCont_of_isArtinianRing B' _
    have e4 := isEquiv_baseChangeAlong_mkStd Aobj B' f hfloc τA hcA hcB'
    have e5 : ρB'.IsEquiv (mkStd B' (mapRepn (Fin 2) _ 𝒪 f τA) hcB') := by
      refine ⟨{ toLinearEquiv := bB'.equivFun, map_apply := fun σ x => ?_ }⟩
      rw [mkStd_ρ_apply, ← hbB' σ]
      show (bB'.equivFun : ρB'.V → (Fin 2 → B')) (ρB'.ρ σ x) = _
      funext i
      simp only [Module.Basis.equivFun_apply]
      rw [← LinearMap.toMatrix_mulVec_repr bB' bB' (ρB'.ρ σ) x]
      rfl
    exact h𝒟.of_isEquiv tB' (isEquiv_trans (isEquiv_trans (isEquiv_trans e3 e4) (isEquiv_symm e5)) ⟨GaloisRepAdic.Equiv.refl _⟩) hDf

  let xτ : (conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.obj Aobj :=
    ⟨Quotient.mk'' τA, τA, hτcond, rfl⟩
  let f : R ⟶ Aobj := e.homEquiv.symm xτ
  have hnat : Subtype.val (e.homEquiv f) =
      (Quotient.mk'' (mapRepn (Fin 2) _ 𝒪 f ρu) : (repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj Aobj) := by
    have hc := e.homEquiv_comp f (𝟙 R)
    rw [Category.id_comp] at hc
    rw [hc]
    show (repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).map f (e.homEquiv (𝟙 R)).1 = _
    rw [← hρu']
    rfl
  have hcls : (Quotient.mk'' (mapRepn (Fin 2) _ 𝒪 f ρu) : (repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj Aobj) =
      Quotient.mk'' τA := by
    rw [← hnat]
    have : e.homEquiv f = xτ := e.homEquiv.apply_symm_apply xτ
    rw [this]

  obtain ⟨⟨γc, hγc⟩, hγsmul⟩ := Quotient.exact' hcls

  have hconj : ∀ σ, ConjAct.ofConjAct γc * τA σ * (ConjAct.ofConjAct γc)⁻¹ = mapRepn (Fin 2) _ 𝒪 f ρu σ := by
    intro σ
    have := congrArg (fun (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) Aobj) => τ σ) hγsmul
    exact this
  have hcf : StdCont Aobj (mapRepn (Fin 2) _ 𝒪 f ρu) := GaloisRepAdic.galoisActionIsAdicContinuous_toLin_of_continuous Aobj _
  have e6 : (mkStd Aobj τA hcA).IsEquiv (mkStd Aobj (mapRepn (Fin 2) _ 𝒪 f ρu) hcf) :=
    isEquiv_mkStd_of_conj Aobj τA _ hcA hcf (ConjAct.ofConjAct γc) hconj

  have hfloc : IsLocalHom f.hom.toRingHom :=
    isLocalHom_of_algHom_of_residue_surjective' (𝒪 := 𝒪) hresA (f.hom : R →ₐ[𝒪] A)
  have hφe : ((f.hom : R →ₐ[𝒪] A) : R →+* A) = f.hom.toRingHom := RingHom.ext fun _ => rfl
  have hφloc : IsLocalHom ((f.hom : R →ₐ[𝒪] A) : R →+* A) := hφe ▸ hfloc
  refine ⟨(f.hom : R →ₐ[𝒪] A), hφloc, ?_⟩
  have e7 := isEquiv_baseChangeAlong_mkStd R Aobj f hfloc ρu
    hcont hcf
  have e8 := isEquiv_baseChangeAlong_congr hφe hφloc hfloc ρR
  exact isEquiv_trans (isEquiv_trans (isEquiv_trans e8 e7) (isEquiv_symm e6)) (isEquiv_symm eA)

end S_GaloisRep_exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy
end P2MW
export P2MW.S_GaloisRep_exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy (solution)
