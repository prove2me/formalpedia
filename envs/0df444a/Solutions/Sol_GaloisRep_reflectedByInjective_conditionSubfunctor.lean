-- Prove2me | solution 1 for GaloisRep.reflectedByInjective_conditionSubfunctor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/01430961-4cdf-5382-9945-d505b2696514

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_ProartinianCompact
import Theorems.Thm_Deformation_reflectedByInjective_liftFunctor
import Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor

set_option autoImplicit false

open CategoryTheory IsLocalRing

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation"

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

noncomputable def stdRep (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B) :
    GaloisRepAdic B where
  V := Fin 2 → B
  finrank_eq := Module.finrank_fin_fun B
  ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)
  isAdicContinuous := by
    haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B
    intro n
    have hcont : Continuous fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) :=
      Units.continuous_val.comp (map_continuous τ)
    have hmem : (fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) ⁻¹' {1} ∈
        nhds (1 : Γℚ) := by
      refine ((isOpen_discrete _).preimage hcont).mem_nhds ?_
      simp
    obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
    refine ⟨L, hL, fun σ hσ v => ?_⟩
    have hσmem : σ ∈ (L.fixingSubgroup : Set Γℚ) := by
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]; exact hσ
    have h1 : ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) = 1 := hsub hσmem
    have hact : ((Units.coeHom _).comp
        (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)) σ v =
        ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).mulVec v := by
      show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup B (Fin 2 → B)) :
        (Fin 2 → B) →ₗ[B] (Fin 2 → B)) v = _
      rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl
    rw [hact, h1, Matrix.one_mulVec, sub_self]
    exact Submodule.zero_mem _

lemma stdRep_ρ_apply (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (σ : Γℚ) (v : Fin 2 → B) :
    (stdRep B τ).ρ σ v = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).mulVec v := by
  show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup B (Fin 2 → B)) :
    (Fin 2 → B) →ₗ[B] (Fin 2 → B)) v = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl

noncomputable def equivStdRepOfBasis (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (ρB : GaloisRepAdic B) (b : Module.Basis (Fin 2) B ρB.V)
    (hb : ∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) :
    GaloisRepAdic.Equiv ρB (stdRep B τ) where
  toLinearEquiv := b.equivFun
  map_apply σ x := by
    rw [stdRep_ρ_apply, ← hb σ]
    show (b.equivFun : ρB.V → (Fin 2 → B)) (ρB.ρ σ x) = _
    funext i
    simp only [Module.Basis.equivFun_apply]
    rw [← LinearMap.toMatrix_mulVec_repr b b (ρB.ρ σ) x]
    rfl

theorem isEquiv_stdRep_of_basis (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (ρB : GaloisRepAdic B) (b : Module.Basis (Fin 2) B ρB.V)
    (hb : ∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) :
    ρB.IsEquiv (stdRep B τ) :=
  ⟨equivStdRepOfBasis B τ ρB b hb⟩

lemma toMatrix_stdRep (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B) (σ : Γℚ) :
    LinearMap.toMatrix (Pi.basisFun B (Fin 2)) (Pi.basisFun B (Fin 2)) ((stdRep B τ).ρ σ) =
      ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  have : (stdRep B τ).ρ σ = Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) :=
    LinearMap.ext fun v => stdRep_ρ_apply B τ σ v
  rw [this, LinearMap.toMatrix_eq_toMatrix']
  have h2 : Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      Matrix.toLin' ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
    apply LinearMap.ext; intro v; rw [Matrix.toLin'_apply]; rfl
  rw [h2, LinearMap.toMatrix'_toLin']

theorem isArtinianTestAlgebra (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    GaloisRep.IsArtinianTestAlgebra 𝒪 B where
  isLocalHom := inferInstance
  residue_surjective := by
    have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (B : Type)
    rwa [IsScalarTower.algebraMap_eq 𝒪 B (ResidueField B), ResidueField.algebraMap_eq, RingHom.coe_comp] at h
  isArtinian := inferInstance

theorem isEquiv_baseChangeAlong_stdRep (B B' : ProartinianCat 𝒪) [IsArtinianRing B] [IsArtinianRing B']
    (f : B ⟶ B') (hf : IsLocalHom f.hom.toRingHom) (τ : Γℚ →ₜ* GL (Fin 2) B) :
    ((stdRep B τ).baseChangeAlong f.hom.toRingHom hf).IsEquiv
      (stdRep B' (mapRepn (Fin 2) Γℚ 𝒪 f τ)) := by
  letI : Algebra B B' := f.hom.toRingHom.toAlgebra
  refine ⟨{ toLinearEquiv := TensorProduct.piScalarRight B B' B' (Fin 2), map_apply := fun σ => ?_ }⟩

  change ∀ x : TensorProduct B B' (Fin 2 → B),
    (TensorProduct.piScalarRight B B' B' (Fin 2))
        (((Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)).baseChange B') x) =
      ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) B') :
          Matrix (Fin 2) (Fin 2) B').mulVec ((TensorProduct.piScalarRight B B' B' (Fin 2)) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, Matrix.mulVec_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mulVec_add]
  | tmul n v =>
    rw [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
    funext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
    have hmap : ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) B') : Matrix (Fin 2) (Fin 2) B')
        = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).map f.hom.toRingHom := by
      rw [Matrix.GeneralLinearGroup.map, Units.coe_map]; rfl
    simp only [hmap, Matrix.map_apply, Matrix.mulVec, dotProduct, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      map_sum, map_mul, Finset.sum_mul, mul_assoc]

end GaloisRep.SolAuxG5

namespace Deformation
p2m_export "Deformation" "mapRepn repnFunctor liftFunctor IsLocalProartinianAlgebra ProartinianCat ProartinianCat.residueField ReflectedByInjective reflectedByInjective_liftFunctor"
p2m_open "Deformation"

variable {𝓞 : Type} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "of ofHom comp_apply residueField algebra carrier mk"
p2m_open "Deformation.ProartinianCat"

variable (B : ProartinianCat 𝓞)

def OpenIdx : Type := {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤}

scoped instance : PartialOrder (OpenIdx B) :=
  inferInstanceAs (PartialOrder {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤})

scoped instance : Nonempty (OpenIdx B) :=
  ⟨⟨maximalIdeal B, isOpen_maximalIdeal_of_isProartinian,
    (maximalIdeal.isMaximal B).ne_top⟩⟩

def OpenIdx.inf (I J : OpenIdx B) : OpenIdx B :=
  ⟨I.1 ⊓ J.1, IsOpen.inter I.2.1 J.2.1,
    fun h ↦ I.2.2 (top_le_iff.mp (h.symm.trans_le inf_le_left))⟩

variable {B} in
omit [IsLocalRing 𝓞] in
lemma OpenIdx.inf_le_left (I J : OpenIdx B) : OpenIdx.inf B I J ≤ I := by
  change I.1 ⊓ J.1 ≤ I.1
  exact _root_.inf_le_left

variable {B} in
omit [IsLocalRing 𝓞] in
lemma OpenIdx.inf_le_right (I J : OpenIdx B) : OpenIdx.inf B I J ≤ J := by
  change I.1 ⊓ J.1 ≤ J.1
  exact _root_.inf_le_right

variable {B} (I : OpenIdx B)

scoped instance quot_nontrivial : Nontrivial (B ⧸ I.1) := Ideal.Quotient.nontrivial_iff.2 I.2.2

scoped instance quot_isLocalRing : IsLocalRing (B ⧸ I.1) :=
  .of_surjective' _ Ideal.Quotient.mk_surjective

scoped instance quot_isArtinianRing : IsArtinianRing (B ⧸ I.1) :=
  IsProartinian.isArtinianRing_quotient I.1 I.2.1

scoped instance quot_discreteTopology : DiscreteTopology (B ⧸ I.1) :=
  QuotientAddGroup.discreteTopology I.2.1

scoped instance quot_isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 (B ⧸ I.1) :=
  haveI : IsLocalHom (Ideal.Quotient.mk I.1) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap 𝓞 (B ⧸ I.1)) := by
    have heq : algebraMap 𝓞 (B ⧸ I.1) = (Ideal.Quotient.mk I.1).comp (algebraMap 𝓞 B) := by
      rw [IsScalarTower.algebraMap_eq 𝓞 B (B ⧸ I.1), Ideal.Quotient.algebraMap_eq]
    rw [heq]
    exact RingHom.isLocalHom_comp _ _
  { }

noncomputable def quotObj : ProartinianCat 𝓞 := of 𝓞 (B ⧸ I.1)

scoped instance [Finite (ResidueField 𝓞)] : Finite (quotObj I) :=
  IsProartinian.finite_quotient_of_isOpen (R := B) I.1 I.2.1

scoped instance : DiscreteTopology (quotObj I) :=
  inferInstanceAs (DiscreteTopology (B ⧸ I.1))

lemma continuous_quotientMk : Continuous (Ideal.Quotient.mk I.1) := by
  refine (RingHom.continuous_iff_isOpen_ker (f := Ideal.Quotient.mk I.1)).mpr ?_
  rw [Ideal.mk_ker]
  exact I.2.1

noncomputable def quotMk : B ⟶ quotObj I :=
  ofHom ⟨Ideal.Quotient.mkₐ 𝓞 I.1, continuous_quotientMk I⟩

@[scoped simp]
lemma quotMk_apply (b : B) : (quotMk I).hom b = Ideal.Quotient.mk I.1 b := rfl

noncomputable def quotFactor {I J : OpenIdx B} (h : I ≤ J) : quotObj I ⟶ quotObj J :=
  ofHom ⟨Ideal.Quotient.factorₐ 𝓞 (h : I.1 ≤ J.1), continuous_of_discreteTopology⟩

@[scoped simp]
lemma quotFactor_mk {I J : OpenIdx B} (h : I ≤ J) (b : B) :
    (quotFactor h).hom (Ideal.Quotient.mk I.1 b) = Ideal.Quotient.mk J.1 b := rfl

@[reassoc (attr := simp)]
lemma quotMk_quotFactor {I J : OpenIdx B} (h : I ≤ J) :
    quotMk I ≫ quotFactor h = quotMk J := by
  ext b
  rfl

noncomputable def quotLiftHom {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) :
    quotObj I ⟶ C :=
  ⟨{ Ideal.Quotient.liftₐ I.1 (g.hom : B →ₐ[𝓞] C) hg with cont := continuous_of_discreteTopology }⟩

lemma quotLiftHom_mk {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) (b : B) :
    (quotLiftHom I g hg).hom (Ideal.Quotient.mk I.1 b) = g.hom b := rfl

lemma quotMk_quotLiftHom {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) :
    quotMk I ≫ quotLiftHom I g hg = g := by
  ext b
  rfl

lemma quotLiftHom_injective {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0)
    (hker : ∀ x, g.hom x = 0 → x ∈ I.1) : Function.Injective (quotLiftHom I g hg).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker b hx)

end ProartinianCat
p2m_reactivate "P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation.ProartinianCat"

end Deformation
p2m_reactivate "P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation.ProartinianCat"

theorem exists_openIdx_comap_le [Finite (ResidueField 𝒪)] {T A : ProartinianCat 𝒪} (ι : T ⟶ A)
    (hι : Function.Injective ι.hom) (J : Ideal T) (hJ : IsOpen (J : Set T)) :
    ∃ J' : OpenIdx A, J'.1.comap ι.hom.toRingHom ≤ J := by
  haveI : T2Space A := inferInstance
  have hemb : Topology.IsClosedEmbedding ι.hom := (ι.hom.cont).isClosedEmbedding hι
  obtain ⟨U, hUopen, hUJ⟩ := hemb.isInducing.isOpen_iff.mp hJ
  have h0U : (0 : A) ∈ U := by
    have : (0 : T) ∈ ι.hom ⁻¹' U := by rw [hUJ]; exact J.zero_mem
    simpa using this
  obtain ⟨J', hJ'open, hJ'U⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp (hUopen.mem_nhds h0U)
  refine ⟨⟨J' ⊓ maximalIdeal A, ?_, ?_⟩, ?_⟩
  · have : ((J' ⊓ maximalIdeal A : Ideal A) : Set A) = (J' : Set A) ∩ (maximalIdeal A : Set A) := rfl
    rw [this]; exact hJ'open.inter isOpen_maximalIdeal_of_isProartinian
  · exact fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ inf_le_right))
  · intro x hx
    have hx' : ι.hom x ∈ J' := (Ideal.mem_comap.mp hx).1
    have : x ∈ ι.hom ⁻¹' U := hJ'U hx'
    rw [hUJ] at this
    exact this

theorem isLocalHom_of_algHom_of_residue_surjective
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

theorem isLocalHom_coe_hom {X Y : ProartinianCat 𝒪} (f : X ⟶ Y) :
    IsLocalHom ((f.hom : X →ₐ[𝒪] Y) : X →+* Y) :=
  isLocalHom_of_algHom_of_residue_surjective (𝒪 := 𝒪)
    (by
      have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (Y : Type)
      rwa [IsScalarTower.algebraMap_eq 𝒪 Y (ResidueField Y), ResidueField.algebraMap_eq, RingHom.coe_comp] at h)
    (f.hom : X →ₐ[𝒪] Y)

theorem isEquiv_symm {B : Type} [CommRing B] [IsLocalRing B] {ρ ρ' : GaloisRepAdic B} (h : ρ.IsEquiv ρ') :
    ρ'.IsEquiv ρ := ⟨h.some.symm⟩

theorem reflectedByInjective_conditionSubfunctor [Finite (ResidueField 𝒪)]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (repnFunctor (Fin 2) Γℚ 𝒪).obj ProartinianCat.residueField)
    (hreflLift : ReflectedByInjective (Fin 2) (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀)) :
    ReflectedByInjective (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀) := by
  classical
  intro T A ι hι σ hσ
  obtain ⟨hlift, hD⟩ := hσ
  refine ⟨hreflLift ι hι hlift, ?_⟩
  intro C _ g ρC b hb

  haveI : DiscreteTopology C := discreteTopology_of_isArtinianRing C
  have hKopen : IsOpen ((RingHom.ker g.hom.toRingHom : Ideal T) : Set T) := by
    have : ((RingHom.ker g.hom.toRingHom : Ideal T) : Set T) = g.hom ⁻¹' {0} := by
      ext x; simp [RingHom.mem_ker]
    rw [this]
    exact (isOpen_discrete _).preimage g.hom.cont
  obtain ⟨J', hJ'⟩ := exists_openIdx_comap_le ι hι _ hKopen

  have hIopen : IsOpen ((J'.1.comap ι.hom.toRingHom : Ideal T) : Set T) := by
    have : ((J'.1.comap ι.hom.toRingHom : Ideal T) : Set T) = ι.hom ⁻¹' (J'.1 : Set A) := rfl
    rw [this]; exact J'.2.1.preimage ι.hom.cont
  have hIne : (J'.1.comap ι.hom.toRingHom : Ideal T) ≠ ⊤ := by
    intro h
    have h1 : (1 : T) ∈ J'.1.comap ι.hom.toRingHom := h ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact J'.2.2 ((Ideal.eq_top_iff_one _).mpr h1)
  let IT : OpenIdx T := ⟨J'.1.comap ι.hom.toRingHom, hIopen, hIne⟩
  let qA : A ⟶ quotObj J' := quotMk J'
  let qT : T ⟶ quotObj IT := quotMk IT

  let ιbar : quotObj IT ⟶ quotObj J' := quotLiftHom IT (ι ≫ qA) (fun x hx => by
    show (qA).hom (ι.hom x) = 0
    rw [quotMk_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp hx))
  have hιbar_inj : Function.Injective ιbar.hom :=
    quotLiftHom_injective IT (ι ≫ qA) _ (fun x hx => by
      have hx' : (qA).hom (ι.hom x) = 0 := hx
      rw [quotMk_apply] at hx'
      exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

  let gbar : quotObj IT ⟶ C := quotLiftHom IT g (fun x hx => (RingHom.mem_ker).mp (hJ' hx))
  have hcomm1 : qT ≫ ιbar = ι ≫ qA := quotMk_quotLiftHom IT _ _
  have hcomm2 : qT ≫ gbar = g := quotMk_quotLiftHom IT _ _

  have hpush1 : mapRepn (Fin 2) Γℚ 𝒪 qA (mapRepn (Fin 2) Γℚ 𝒪 ι σ) =
      mapRepn (Fin 2) Γℚ 𝒪 ιbar (mapRepn (Fin 2) Γℚ 𝒪 qT σ) := by
    simp only [mapRepn]
    rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map ι) ((repnFunctor (Fin 2) Γℚ 𝒪).map qA),
      ← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qT) ((repnFunctor (Fin 2) Γℚ 𝒪).map ιbar),
      ← Functor.map_comp, ← Functor.map_comp, hcomm1]
  have hpush2 : mapRepn (Fin 2) Γℚ 𝒪 gbar (mapRepn (Fin 2) Γℚ 𝒪 qT σ) = mapRepn (Fin 2) Γℚ 𝒪 g σ := by
    simp only [mapRepn]
    rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qT) ((repnFunctor (Fin 2) Γℚ 𝒪).map gbar),
      ← Functor.map_comp, hcomm2]

  have tA' := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj J')
  have tT' := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj IT)
  have tC := isArtinianTestAlgebra (𝒪 := 𝒪) C
  have hιloc : IsLocalHom ιbar.hom.toRingHom := isLocalHom_coe_hom ιbar
  have hgloc : IsLocalHom gbar.hom.toRingHom := isLocalHom_coe_hom gbar

  have hDA' : 𝒟 (stdRep (quotObj J') (mapRepn (Fin 2) Γℚ 𝒪 qA (mapRepn (Fin 2) Γℚ 𝒪 ι σ))) :=
    hD (quotObj J') qA _ (Pi.basisFun _ _) (toMatrix_stdRep _ _)
  rw [hpush1] at hDA'

  have e1 := isEquiv_baseChangeAlong_stdRep (quotObj IT) (quotObj J') ιbar hιloc (mapRepn (Fin 2) Γℚ 𝒪 qT σ)
  have hDbc : 𝒟 ((stdRep (quotObj IT) (mapRepn (Fin 2) Γℚ 𝒪 qT σ)).baseChangeAlong ιbar.hom.toRingHom hιloc) :=
    h𝒟.of_isEquiv tA' (isEquiv_symm e1) hDA'

  have hDT' : 𝒟 (stdRep (quotObj IT) (mapRepn (Fin 2) Γℚ 𝒪 qT σ)) :=
    h𝒟.of_baseChangeAlong_injective tT' tA' (ιbar.hom : quotObj IT →ₐ[𝒪] quotObj J') hιloc hιbar_inj hDbc

  have hDbc2 := h𝒟.baseChangeAlong tT' tC (gbar.hom : quotObj IT →ₐ[𝒪] C) hgloc hDT'
  have e2 := isEquiv_baseChangeAlong_stdRep (quotObj IT) C gbar hgloc (mapRepn (Fin 2) Γℚ 𝒪 qT σ)
  have hDstdC : 𝒟 (stdRep C (mapRepn (Fin 2) Γℚ 𝒪 g σ)) := by
    rw [← hpush2]; exact h𝒟.of_isEquiv tC e2 hDbc2

  exact h𝒟.of_isEquiv tC (isEquiv_symm (isEquiv_stdRep_of_basis C _ ρC b hb)) hDstdC

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation"
p2m_reactivate "P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation"

open _root_.Deformation _root_.P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.Deformation GaloisRep.SolAuxG5 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField)
    [Finite (IsLocalRing.ResidueField 𝒪)]
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟) :
    Deformation.ReflectedByInjective (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀) :=
  reflectedByInjective_conditionSubfunctor 𝒟 h𝒟 ρ₀ (Deformation.reflectedByInjective_liftFunctor ρ₀)

end S_GaloisRep_reflectedByInjective_conditionSubfunctor
end P2MW
export P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor (solution)
