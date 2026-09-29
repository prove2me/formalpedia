-- Prove2me | solution 1 for GaloisRep.isOfType_framed_of_mem_conditionLifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f5a796c9-febf-5d64-ac33-07b1695cd17e

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact
import Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_isOfType_framed_of_mem_conditionLifts

set_option autoImplicit false
set_option maxHeartbeats 0

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts"
namespace SolAuxRow
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

theorem toMatrix_mkStd (Y : ProartinianCat 𝒪) (τ : Γℚ →ₜ* GL (Fin 2) Y) (hc : StdCont Y τ) (σ : Γℚ) :
    LinearMap.toMatrix (Pi.basisFun Y (Fin 2)) (Pi.basisFun Y (Fin 2)) ((mkStd Y τ hc).ρ σ) =
      ((τ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) := by
  have h : (mkStd Y τ hc).ρ σ = Matrix.toLin' ((τ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y) := by
    apply LinearMap.ext; intro v; rw [mkStd_ρ_apply]; exact (Matrix.toLin'_apply _ _).symm
  rw [h, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem isEquiv_mkStd_of_toMatrix (Y : ProartinianCat 𝒪) (τ : Γℚ →ₜ* GL (Fin 2) Y) (hc : StdCont Y τ)
    (ρY : GaloisRepAdic Y) (bY : Module.Basis (Fin 2) Y ρY.V)
    (hb : ∀ σ, LinearMap.toMatrix bY bY (ρY.ρ σ) = ((τ σ : GL (Fin 2) Y) : Matrix (Fin 2) (Fin 2) Y)) :
    ρY.IsEquiv (mkStd Y τ hc) := by
  refine ⟨{ toLinearEquiv := bY.equivFun, map_apply := fun σ x => ?_ }⟩
  rw [mkStd_ρ_apply, ← hb σ]
  show (bY.equivFun : ρY.V → (Fin 2 → Y)) (ρY.ρ σ x) = _
  funext i
  simp only [Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr bY bY (ρY.ρ σ) x]
  rfl

theorem isArtinianTestAlgebra_aux_residue (B : ProartinianCat 𝒪) :
    Function.Surjective (IsLocalRing.residue B ∘ algebraMap 𝒪 B) := by
  have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (B : Type)
  rwa [IsScalarTower.algebraMap_eq 𝒪 B (ResidueField B), ResidueField.algebraMap_eq, RingHom.coe_comp] at h

end GaloisRep.SolAuxRow

open GaloisRep.SolAuxRow in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    {R : Deformation.ProartinianCat 𝒪} [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsLocalRing.IsAdicTopology R]
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ R)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom))) :
    𝒟 ({ V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont } : GaloisRepAdic R) := by
  classical
  let ρR : GaloisRepAdic R := mkStd R ρu hcont
  show 𝒟 ρR
  have hresR : Function.Surjective (residue R ∘ algebraMap 𝒪 R) := isArtinianTestAlgebra_aux_residue (𝒪 := 𝒪) R
  refine (h𝒟.iff_forall_surjective (inferInstance : IsLocalHom (algebraMap 𝒪 R)) hresR ρR).mpr ?_
  intro B _ _ _ tB q hq hqs
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : IsArtinianRing B := tB.isArtinian
  haveI : IsLocalHom (algebraMap 𝒪 B) := tB.isLocalHom
  haveI : IsTopologicalRing B := inferInstance
  haveI : IsResidueAlgebra 𝒪 B := ⟨by
    have h := tB.residue_surjective
    rwa [IsScalarTower.algebraMap_eq 𝒪 B (ResidueField B), ResidueField.algebraMap_eq, RingHom.coe_comp]⟩
  haveI : IsLocalProartinianAlgebra 𝒪 B := ⟨⟩
  let Bobj : ProartinianCat 𝒪 := ProartinianCat.of 𝒪 B
  haveI : IsArtinianRing Bobj := tB.isArtinian
  haveI := hq
  have hqcont : Continuous q := isContinuous_of_isProartinian_of_isLocalHom (q : R →+* B)
  let qm : R ⟶ Bobj := ⟨⟨q, hqcont⟩⟩
  have hqe : (q : R →+* B) = qm.hom.toRingHom := RingHom.ext fun _ => rfl
  have hqloc : IsLocalHom qm.hom.toRingHom := hqe ▸ hq
  have hcB : StdCont Bobj (mapRepn (Fin 2) _ 𝒪 qm ρu) := stdCont_of_isArtinianRing Bobj _
  have hDstd : 𝒟 (mkStd Bobj (mapRepn (Fin 2) _ 𝒪 qm ρu) hcB) :=
    hρu.2 Bobj qm _ (Pi.basisFun _ _) (toMatrix_mkStd Bobj _ hcB)
  have e1 := isEquiv_baseChangeAlong_mkStd R Bobj qm hqloc ρu hcont hcB
  have e2 := isEquiv_baseChangeAlong_congr hqe hq hqloc ρR
  have tBobj : GaloisRep.IsArtinianTestAlgebra 𝒪 (Bobj : Type) := tB
  exact h𝒟.of_isEquiv tBobj (isEquiv_symm (isEquiv_trans e2 e1)) hDstd

end S_GaloisRep_isOfType_framed_of_mem_conditionLifts
end P2MW
export P2MW.S_GaloisRep_isOfType_framed_of_mem_conditionLifts (solution)
