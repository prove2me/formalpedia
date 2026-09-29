-- Prove2me | solution 1 for CerednikDrinfeld.QM.RigidifiedPairClass.exists_stratumPoint_of_forall_representsOn_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0a7a08cb-f17b-5597-8c2e-4d9b3eef9f3f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsogenyPair_existsUnique_hom_isPullback_of_representsOn
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepS14

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem specMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem specMap_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

private theorem _root_.RelRepS14.specMap_algebraMap_self (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R)) := by
  exact specMap_id R

p2m_export "RelRepS14" "specMap_algebraMap_self"
theorem lev_converse {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f)
    (hP : ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) : FactorsThrough E'.lev P := by
  obtain ⟨hg, hmul, -, hlev⟩ := h
  exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ E E' g hg hmul hlev t' P hP

theorem exists_comparison {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (E : FakeEllipticCurve Λ N S)
    (E₁ E₂ : FakeEllipticCurve Λ N S') (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E E₁ g₁)
    (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia φ E E₂ g₂) :
    ∃ k : E₂.A ⟶ E₁.A, k ≫ g₁ = g₂ ∧ FakeEllipticCurve.IsPullbackVia (RingHom.id S') E₁ E₂ k := by
  obtain ⟨k, hkg, -, -, hk⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq φ (RingHom.id S') φ
      (RingHom.id_comp φ) E E₁ E₂ g₁ h₁ (fun t' P hP => lev_converse φ E E₁ g₁ h₁ t' P hP) g₂ h₂
  exact ⟨k, hkg, hk⟩

theorem exists_factor {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (χ : S →+* S'') (hχ : ψ.comp φ = χ) (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (g' : E'.A ⟶ E.A) (h' : FakeEllipticCurve.IsPullbackVia φ E E' g')
    (E'' : FakeEllipticCurve Λ N S'') (g : E''.A ⟶ E.A) (h : FakeEllipticCurve.IsPullbackVia χ E E'' g) :
    ∃ k : E''.A ⟶ E'.A, k ≫ g' = g ∧ FakeEllipticCurve.IsPullbackVia ψ E' E'' k := by
  obtain ⟨k, hkg, -, -, hk⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq φ ψ χ hχ E E' E'' g' h'
      (fun t' P hP => lev_converse φ E E' g' h' t' P hP) g h
  exact ⟨k, hkg, hk⟩

section Base

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
  (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]

theorem le_comap : Ideal.span {algebraMap 𝒪 C π} ≤ (Ideal.span {algebraMap 𝒪 T π}).comap (algebraMap C T) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
  exact Ideal.subset_span rfl

private def _root_.RelRepS14.qmap : (C ⧸ Ideal.span {algebraMap 𝒪 C π}) →+* (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := Ideal.quotientMap _ (algebraMap C T) (le_comap π C T)

p2m_export "RelRepS14" "qmap"
theorem qmap_comp_mk : (qmap π C T).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (algebraMap C T) := by
  ext x; rfl

abbrev algq : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := (qmap π C T).toAlgebra

theorem tower : letI := algq π C T; IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := by
  letI := algq π C T
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  change Ideal.Quotient.mk _ (algebraMap 𝒪 T x) = Ideal.Quotient.mk _ (algebraMap C T (algebraMap 𝒪 C x))
  rw [← IsScalarTower.algebraMap_apply]

theorem ideal_eq : Ideal.span {algebraMap C T (algebraMap 𝒪 C π)} = Ideal.span {algebraMap 𝒪 T π} := by
  rw [← IsScalarTower.algebraMap_apply]

def eqq : (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) ≃+* (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := Ideal.quotEquivOfEq (ideal_eq π C T)

theorem eqq_symm_comp_mk : (eqq π C T).symm.toRingHom.comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _ := by
  ext x; rfl

end Base

section Frame

theorem residueLeg_eq (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) :
    (qmap π C T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = FakeEllipticCurve.Rigidification.residueLeg π ψT := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  change ((qmap π C T).comp (Ideal.Quotient.mk _)) ((ψ : Onr →+* C) x) = Ideal.Quotient.mk _ ((ψT : Onr →+* T) x)
  rw [qmap_comp_mk, RingHom.comp_apply, hψT]
  rfl

def uq (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : FakeEllipticCurve.WithFullLevel Λ N n (T ⧸ Ideal.span {algebraMap 𝒪 T π}) :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose

def gu (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1.A ⟶ u.1.A :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose_spec.choose

theorem gu_spec (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) :
    FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ∧
    ((uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).1 ≫ gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (u.2.P).1 := by
  obtain ⟨hg, hmul, hact, hlev, -, hgen⟩ := (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose_spec.choose_spec
  exact ⟨⟨hg, hmul, hact, hlev⟩, hgen⟩

theorem uq_isPullback (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : FakeEllipticCurve.WithFullLevel.IsPullback (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := by
  obtain ⟨hg, hmul, hact, hlev, -, hgen⟩ := (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose_spec.choose_spec
  exact ⟨gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, hg, hmul, hact, hlev, hgen⟩

def gE (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : ρ.Eb.A ⟶ (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1.A :=
  (exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Eb (gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1
    ρ.gb ρ.isPullback_Eb).choose

theorem gE_spec (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ = ρ.gb ∧
    FakeEllipticCurve.IsPullbackVia (RingHom.id _) (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Eb (gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :=
  (exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Eb (gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1
    ρ.gb ρ.isPullback_Eb).choose_spec

private def _root_.RelRepS14.gA (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : ρ.Ab.A ⟶ 𝔄.A :=
  (exists_factor (FakeEllipticCurve.Rigidification.residueLeg π ψ) (qmap π C T) _ (residueLeg_eq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)
    A₀ 𝔄 g𝔄 h𝔄 ρ.Ab ρ.gA ρ.isPullback_Ab).choose

p2m_export "RelRepS14" "gA"
theorem gA_spec (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ g𝔄 = ρ.gA ∧
    FakeEllipticCurve.IsPullbackVia (qmap π C T) 𝔄 ρ.Ab (gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :=
  (exists_factor (FakeEllipticCurve.Rigidification.residueLeg π ψ) (qmap π C T) _ (residueLeg_eq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)
    A₀ 𝔄 g𝔄 h𝔄 ρ.Ab ρ.gA ρ.isPullback_Ab).choose_spec

theorem loc (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : letI := algq π C T
    ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) (_ : LocallyOfFinitePresentation ξ)
      (pt : FakeEllipticCurve.IsogenyPair.PtFamily r ρ.d (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Ab ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r ρ.d (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Ab ξ pt :=
  letI := algq π C T; haveI := tower π C T
  hloc ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2

def X (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : Scheme.{0} := (loc r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).choose

def ξ (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})) := (loc r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).choose_spec.choose

theorem lfp (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : LocallyOfFinitePresentation (ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := (loc r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).choose_spec.choose_spec.choose

def pt (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : letI := algq π C T
    FakeEllipticCurve.IsogenyPair.PtFamily r ρ.d (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Ab (ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :=
  (loc r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).choose_spec.choose_spec.choose_spec.choose

theorem hX (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : letI := algq π C T
    FakeEllipticCurve.IsogenyPair.RepresentsOn r ρ.d (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ρ.Ab (ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :=
  (loc r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).choose_spec.choose_spec.choose_spec.choose_spec

def p0 (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) (ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :=
  pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ (T ⧸ Ideal.span {algebraMap 𝒪 T π}) ρ.Eb ρ.Ab (gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 ρ.Ab.A)
    (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ.Ab) ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel

theorem p0_over (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : (p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ≫ ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ = 𝟙 _ := by
  rw [(p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2]; exact specMap_algebraMap_self _

def x0 (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})) ⟶ Xbar ρ.d :=
  letI := algq π C T; haveI := tower π C T
  (p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    (X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)

theorem x0_fst (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ qbar ρ.d ≫ pullback.fst fM _ =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 := by
  letI := algq π C T; haveI := tower π C T
  unfold x0
  rw [Category.assoc, (hB1 ρ.d _ _ _ _ _ _ _ _ _).1, ← Category.assoc, p0_over r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, Category.id_comp]
  exact hM.ptF_pullback T _ (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) _ _ (by rw [← specMap_comp]) u _
    (uq_isPullback r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)

theorem x0_snd (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ qbar ρ.d ≫ pullback.snd fM _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C T)) := by
  letI := algq π C T; haveI := tower π C T
  unfold x0
  rw [Category.assoc, reassoc_of% (hB1 ρ.d _ _ _ _ _ _ _ _ _).2, ← Category.assoc, p0_over r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, Category.id_comp,
    ← specMap_comp, ← specMap_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (qmap_comp_mk π C T)

def xPt (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ Xbar ρ.d :=
  Spec.map (CommRingCat.ofHom (eqq π C T).symm.toRingHom) ≫ x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ

theorem xPt_fst (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) :
    xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ qbar ρ.d ≫ pullback.fst fM _ =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫
      (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 := by
  unfold xPt
  rw [Category.assoc, x0_fst r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, ← Category.assoc, ← specMap_comp, eqq_symm_comp_mk]

theorem xPt_snd (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) :
    xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ qbar ρ.d ≫ pullback.snd fM _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C T)) := by
  unfold xPt
  rw [Category.assoc, x0_snd r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, ← Category.assoc, ← specMap_comp, eqq_symm_comp_mk]

theorem ptF_congr (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) {S : Type} [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (e : s₁ = s₂) (w : FakeEllipticCurve.WithFullLevel Λ N n S) : (ptF S s₁ w).1 = (ptF S s₂ w).1 := by
  subst e; rfl

theorem xPt_over (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (ι : pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ pullback.fst fM _ = pullback.fst fM _)
    (hι₂ : ι ≫ pullback.snd fM _ = pullback.snd fM _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (t : Spec (CommRingCat.of T) ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (ht₁ : t ≫ pullback.fst fM _ =
      (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1)
    (ht₂ : t ≫ pullback.snd fM _ = Spec.map (CommRingCat.ofHom (algebraMap C T))) :
    xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ (qbar ρ.d ≫ ι) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t := by
  have hs : Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T)) := by
    rw [← specMap_comp, ← IsScalarTower.algebraMap_eq]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hι₁, xPt_fst r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, ht₁, ptF_congr r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ _ _ hs u]
  · simp only [Category.assoc]
    rw [hι₂, xPt_snd r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ, ht₂]

end Frame

end RelRepS14

end

namespace Alg5X4

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem specMap_ofHom_id (S : Type) [CommRing S] :
    Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem mul_val_congr' {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem over_of_isPullbackVia_id {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) (k : E'.A ⟶ E.A)
    (h : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E' k) : k ≫ E.f = E'.f := by
  obtain ⟨hsq, -, -, -⟩ := h
  have := hsq.w
  rw [specMap_ofHom_id, Category.comp_id] at this
  exact this

theorem isPullbackVia_id_of_isoVia {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : FakeEllipticCurve.IsoVia E E' i hi) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E' E i.hom := by
  obtain ⟨hmul, hact, hlev⟩ := h
  have hsq : IsPullback i.hom E.f E'.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [specMap_ofHom_id]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hi]⟩
  refine ⟨hsq, ?_, ?_, ?_⟩
  · intro T t P Q
    have hm := congrArg Subtype.val (hmul t P Q)
    simp only [mapPt_coe] at hm
    rw [hm]
    exact mul_val_congr' E'.L (by rw [specMap_ofHom_id, Category.comp_id]) _ _ _ _ (by simp [mapPt_coe]) (by simp [mapPt_coe])
  · exact hact
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := (hlev t P).1 hP
    exact ⟨P₀, by rw [hP₀, mapPt_coe]⟩

theorem isoVia_symm {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : FakeEllipticCurve.IsoVia E E' i hi)
    (hi' : i.inv ≫ E.f = E'.f) :
    FakeEllipticCurve.IsoVia E' E i.symm hi' := by
  obtain ⟨hmul, hact, hlev⟩ := h
  have hback : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E'.f),
      mapPt i.hom hi (mapPt i.inv hi' P) = P := fun P => Subtype.ext (by simp [mapPt_coe])
  have hforth : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt i.inv hi' (mapPt i.hom hi P) = P := fun P => Subtype.ext (by simp [mapPt_coe])
  refine ⟨?_, ?_, ?_⟩
  · intro T t P Q
    have hm := hmul t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [hback, hback] at hm
    show mapPt i.inv hi' (E'.L.mul t P Q) = E.L.mul t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [← hm, hforth]
  · intro x
    show E'.act x ≫ i.inv = i.inv ≫ E.act x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hact, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro T t P
    show FactorsThrough E'.lev P ↔ FactorsThrough E.lev (mapPt i.inv hi' P)
    rw [hlev t (mapPt i.inv hi' P), hback]

theorem isPullbackVia_id_of_isoVia_inv {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : FakeEllipticCurve.IsoVia E E' i hi) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E' i.inv := by
  have hi' : i.inv ≫ E.f = E'.f := by rw [Iso.inv_comp_eq, hi]
  exact isPullbackVia_id_of_isoVia E' E i.symm hi' (isoVia_symm E E' i hi h hi')

theorem isoVia_of_isPullbackVia_id {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (k : E.A ⟶ E'.A) (k' : E'.A ⟶ E.A)
    (hk : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E' E k) (hk' : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E' k')
    (h₁ : k ≫ k' = 𝟙 _) (h₂ : k' ≫ k = 𝟙 _) (hi : k ≫ E'.f = E.f) :
    FakeEllipticCurve.IsoVia E E' ⟨k, k', h₁, h₂⟩ hi := by
  obtain ⟨hsq, hmul, hact, hlev⟩ := hk
  obtain ⟨hsq', hmul', hact', hlev'⟩ := hk'
  refine ⟨?_, ?_, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [hmul t P Q]
    exact mul_val_congr' E'.L (by rw [specMap_ofHom_id, Category.comp_id]) _ _ _ _ (by simp [mapPt_coe]) (by simp [mapPt_coe])
  · exact hact
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := hlev t P hP
      exact ⟨P₀, by rw [hP₀, mapPt_coe]⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := hlev' t (mapPt k hi P) hP
      refine ⟨P₀, ?_⟩
      rw [hP₀, mapPt_coe, Category.assoc]
      change P.1 ≫ (k ≫ k') = P.1
      rw [h₁, Category.comp_id]

theorem comp_eq_id_of_comparisons {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E₁ E₂ : FakeEllipticCurve Λ N S')
    (g₁ : E₁.A ⟶ E.A) (hsq₁ : IsPullback g₁ E₁.f E.f (Spec.map (CommRingCat.ofHom φ))) (g₂ : E₂.A ⟶ E.A)
    (k : E₂.A ⟶ E₁.A) (hk : k ≫ g₁ = g₂) (hkf : k ≫ E₁.f = E₂.f)
    (k' : E₁.A ⟶ E₂.A) (hk' : k' ≫ g₂ = g₁) (hk'f : k' ≫ E₂.f = E₁.f) :
    k' ≫ k = 𝟙 _ :=
  hsq₁.hom_ext (by rw [Category.assoc, hk, hk', Category.id_comp]) (by rw [Category.assoc, hkf, hk'f, Category.id_comp])

theorem isIso_specMap_quotient_mk_of_eq_zero {T : Type} [CommRing T] (x : T) (hx : x = 0) :
    IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {x})))) := by
  have hI : Ideal.span {x} = ⊥ := by rw [Ideal.span_singleton_eq_bot]; exact hx
  have hmk_bij : Function.Bijective (Ideal.Quotient.mk (Ideal.span {x})) :=
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, hI]), Ideal.Quotient.mk_surjective⟩
  let ek : T ≃+* (T ⧸ Ideal.span {x}) := RingEquiv.ofBijective (Ideal.Quotient.mk (Ideal.span {x})) hmk_bij
  have hek : (ek : T →+* T ⧸ Ideal.span {x}) = Ideal.Quotient.mk (Ideal.span {x}) := rfl
  rw [← hek]
  change IsIso (Spec.map ek.toCommRingCatIso.hom)
  infer_instance

theorem isoVia_symm' {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (h : FakeEllipticCurve.IsoVia E E' i hi) :
    ∃ hi' : i.inv ≫ E.f = E'.f, FakeEllipticCurve.IsoVia E' E i.symm hi' :=
  ⟨by rw [Iso.inv_comp_eq, hi], isoVia_symm E E' i hi h _⟩

theorem isPullbackVia_id_of_isoVia_withFullLevel {S : Type} [CommRing S] {n : ℕ}
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (h : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) u'.1 u.1 i.hom ∧
      (u.2.P).1 ≫ i.hom = Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ (u'.2.P).1 := by
  obtain ⟨hmul, hact, hlev, hP⟩ := h
  refine ⟨isPullbackVia_id_of_isoVia u.1 u'.1 i hi ⟨hmul, hact, hlev⟩, ?_⟩
  have hP1 := congrArg Subtype.val hP
  rw [mapPt_coe] at hP1
  rw [specMap_ofHom_id, Category.id_comp]
  exact hP1

theorem iso_of_isPullbackVia_id {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (g : E'.A ⟶ E.A) (h : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E' g) :
    ∃ (i : E'.A ≅ E.A) (hi : i.hom ≫ E.f = E'.f), i.hom = g ∧ FakeEllipticCurve.IsoVia E' E i hi := by
  obtain ⟨hsq, hmul, hact, hlev⟩ := h
  have hgf : g ≫ E.f = E'.f := by
    have hw := hsq.w
    rw [specMap_ofHom_id, Category.comp_id] at hw
    exact hw
  have hsq' := hsq
  rw [specMap_ofHom_id] at hsq'
  haveI : IsIso g := hsq'.isIso_fst_of_isIso
  refine ⟨asIso g, hgf, rfl, ?_, ?_, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    simp only [mapPt_coe, asIso_hom]
    rw [hmul t P Q]
    exact mul_val_congr' E.L (by rw [specMap_ofHom_id, Category.comp_id]) _ _ _ _ (by simp [mapPt_coe])
      (by simp [mapPt_coe])
  · intro x
    show E'.act x ≫ g = g ≫ E.act x
    exact hact x
  · intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := hlev t P hP
      exact ⟨P₀, by rw [hP₀, mapPt_coe, asIso_hom]⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := hP
      rw [mapPt_coe, asIso_hom] at hP₀
      exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback (RingHom.id S) E E' g hsq hmul hlev t P
        ⟨P₀, hP₀⟩

end Alg5X4

namespace RelRepX

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem specMap_algebraMap_self (S : Type) [CommRing S] :
    Spec.map (CommRingCat.ofHom (algebraMap S S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [show algebraMap S S = RingHom.id S from rfl, CommRingCat.ofHom_id]; exact Spec.map_id _

theorem pt_congr (r d : ℕ) {S : Type} [CommRing S] {E A : FakeEllipticCurve Λ N S}
    {X : Scheme.{0}} {ξ : X ⟶ Spec (CommRingCat.of S)} (pt : IsogenyPair.PtFamily r d E A ξ)
    (T : Type) [CommRing T] [Algebra S T] (E' A' : FakeEllipticCurve Λ N T)
    (gE₁ gE₂ : E'.A ⟶ E.A) (hE : gE₁ = gE₂)
    (h₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE₁) (h₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE₂)
    (gA₁ gA₂ : A'.A ⟶ A.A) (hA : gA₁ = gA₂)
    (k₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₁) (k₂ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA₂)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    pt T E' A' gE₁ h₁ gA₁ k₁ φ φ' hφ hp hl = pt T E' A' gE₂ h₂ gA₂ k₂ φ φ' hφ hp hl := by
  subst hE hA; rfl

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem ptext {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {gg : X ⟶ Y} {fY : Y ⟶ Z}
    {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback gg fX fY s)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX) (h : P.1 ≫ gg = Q.1 ≫ gg) : P = Q :=
  Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

theorem lev_converse {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f)
    (hP : ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) : FactorsThrough E'.lev P := by
  obtain ⟨hg, hmul, -, hlev⟩ := h
  exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ E E' g hg hmul hlev t' P hP

theorem exists_pullPair {U D : Type} [CommRing U] [CommRing D] (p : U →+* D)
    (dd : ℕ) (E' A' : FakeEllipticCurve Λ N U) (E'' A'' : FakeEllipticCurve Λ N D)
    (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair dd E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    ∃ (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f),
      FakeEllipticCurve.IsIsogenyPair dd E'' A'' ψ ψ' ∧ FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ ∧
        ψ ≫ hA = hE ≫ φ ∧ ψ' ≫ hE = hA ≫ φ' := by
  have hhA₀ := hhA
  obtain ⟨hsqE, Emul, Eact, Elev⟩ := hhE
  obtain ⟨hsqA, Amul, Aact, Alev⟩ := hhA
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := hp
  let ψ : E''.A ⟶ A''.A := hsqA.lift (hE ≫ φ) E''.f (by rw [Category.assoc, hφo]; exact hsqE.w)
  have hψ₁ : ψ ≫ hA = hE ≫ φ := hsqA.lift_fst _ _ _
  have hψ₂ : ψ ≫ A''.f = E''.f := hsqA.lift_snd _ _ _
  let ψ' : A''.A ⟶ E''.A := hsqE.lift (hA ≫ φ') A''.f (by rw [Category.assoc, hφ'o]; exact hsqA.w)
  have hψ'₁ : ψ' ≫ hE = hA ≫ φ' := hsqE.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ E''.f = A''.f := hsqE.lift_snd _ _ _
  have ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t E''.f),
      mapPt ψ hψ₂ (E''.L.mul t P Q) = A''.L.mul t (mapPt ψ hψ₂ P) (mapPt ψ hψ₂ Q) := by
    intro T t P Q
    apply ptext hsqA
    rw [mapPt_coe, Category.assoc, hψ₁, ← Category.assoc, Emul, Amul]
    have := congrArg Subtype.val (hφmul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ₁])
      (by simp only [mapPt_coe, Category.assoc, hψ₁])
  have ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t A''.f),
      mapPt ψ' hψ'₂ (A''.L.mul t P Q) = E''.L.mul t (mapPt ψ' hψ'₂ P) (mapPt ψ' hψ'₂ Q) := by
    intro T t P Q
    apply ptext hsqE
    rw [mapPt_coe, Category.assoc, hψ'₁, ← Category.assoc, Amul, Emul]
    have := congrArg Subtype.val (hφ'mul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ'₁])
      (by simp only [mapPt_coe, Category.assoc, hψ'₁])
  have ψ_act : ∀ x : ↥Λ, E''.act x ≫ ψ = ψ ≫ A''.act x := by
    intro x
    apply hsqA.hom_ext
    · rw [Category.assoc, hψ₁, ← Category.assoc, Eact, Category.assoc, hφlin, Category.assoc, Aact, ← Category.assoc ψ hA, hψ₁,
        Category.assoc]
    · rw [Category.assoc, hψ₂, E''.act_over, Category.assoc, A''.act_over, hψ₂]
  have ψ'_act : ∀ x : ↥Λ, A''.act x ≫ ψ' = ψ' ≫ E''.act x := by
    intro x
    apply hsqE.hom_ext
    · rw [Category.assoc, hψ'₁, ← Category.assoc, Aact, Category.assoc, hφ'lin, Category.assoc, Eact, ← Category.assoc ψ' hE, hψ'₁,
        Category.assoc]
    · rw [Category.assoc, hψ'₂, A''.act_over, Category.assoc, E''.act_over, hψ'₂]
  have ψ_deg : ∀ hm : (((dd : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      ψ ≫ ψ' = E''.act ⟨_, hm⟩ ∧ ψ' ≫ ψ = A''.act ⟨_, hm⟩ := by
    intro hm
    obtain ⟨h1, h2⟩ := hdeg hm
    constructor
    · apply hsqE.hom_ext
      · rw [Category.assoc, hψ'₁, ← Category.assoc, hψ₁, Category.assoc, h1, Eact]
      · rw [Category.assoc, hψ'₂, hψ₂, E''.act_over]
    · apply hsqA.hom_ext
      · rw [Category.assoc, hψ₁, ← Category.assoc, hψ'₁, Category.assoc, h2, Aact]
      · rw [Category.assoc, hψ₂, hψ'₂, A''.act_over]
  have ψ_lev : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ₂ := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := Elev t P hP
    have hQ := hl (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    obtain ⟨Q₀, hQ₀⟩ := hQ
    apply lev_converse p A' A'' hA hhA₀ t (mapPt ψ hψ₂ P)
    exact ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, hψ₁]⟩
  exact ⟨ψ, ψ', hψ₂, ⟨hψ₂, hψ'₂, ψ_hom, ψ'_hom, ψ_act, ψ'_act, ψ_deg⟩, ψ_lev, hψ₁, hψ'₁⟩

section

variable (r d : ℕ) (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
  (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (𝔄 : FakeEllipticCurve Λ N C)
  (Xd : Scheme.{0}) (q : Xd ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
  (κ : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
    FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xd))

theorem kappa_congr
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S)
    (gA₁ gA₂ : A.A ⟶ 𝔄.A) (h : gA₁ = gA₂)
    (h₁ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₁) (h₂ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA₂)
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : IsogenyPair.PtFamily r d u.1 A ξ) (hX : IsogenyPair.RepresentsOn r d u.1 A ξ pt) :
    κ S u A gA₁ h₁ X ξ pt hX = κ S u A gA₂ h₂ X ξ pt hX := by
  subst h; rfl

theorem kappa_pt_comp (hB3 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ S u A gA hgA X ξ pt hX = κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
    [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
    (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
    (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
    (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : IsogenyPair.PtFamily r d u.1 A ξ) (hX : IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
    (pt' : IsogenyPair.PtFamily r d u'.1 A' ξ') (hX' : IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')

    (E₁ A₁ : FakeEllipticCurve Λ N S') (gE₁ : E₁.A ⟶ u'.1.A) (hgE₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S' S') u'.1 E₁ gE₁)
    (gA₁ : A₁.A ⟶ A'.A) (hgA₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S' S') A' A₁ gA₁)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 E₁ (gE₁ ≫ g))
    (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A₁ (gA₁ ≫ hA))
    (φ : E₁.A ⟶ A₁.A) (φ' : A₁.A ⟶ E₁.A) (hφ : φ ≫ A₁.f = E₁.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₁ A₁ φ φ') (hl : FakeEllipticCurve.PreservesLevel E₁ A₁ φ hφ) :
    (pt' S' E₁ A₁ gE₁ hgE₁ gA₁ hgA₁ φ φ' hφ hp hl).1 ≫ κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX' =
      (pt S' E₁ A₁ (gE₁ ≫ g) hgE (gA₁ ≫ hA) hgAA φ φ' hφ hp hl).1 ≫ κ S u A gA hgA X ξ pt hX := by
  obtain ⟨e, ⟨he, hc⟩, -⟩ :=
    IsogenyPair.existsUnique_hom_isPullback_of_representsOn r d S u.1 A X ξ pt hX S' u'.1 A' g hg hA hhA X' ξ' pt' hX'
  rw [← hB3 S S' u u' g hg hP A gA hgA A' hA hhA hgA' X ξ pt hX X' ξ' pt' hX' e he hc, ← Category.assoc,
    hc S' E₁ A₁ gE₁ hgE₁ gA₁ hgA₁ hgE hgAA φ φ' hφ hp hl]

theorem kappa_pt_natural (hB3 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ S u A gA hgA X ξ pt hX = κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
    [Algebra S S'] [IsScalarTower C S S'] [IsScalarTower 𝒪 S S']
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
    (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
    (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
    (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap C S') 𝔄 A' (hA ≫ gA))
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : IsogenyPair.PtFamily r d u.1 A ξ) (hX : IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
    (pt' : IsogenyPair.PtFamily r d u'.1 A' ξ') (hX' : IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')

    (E₀ A₀' : FakeEllipticCurve Λ N S) (gE₀ : E₀.A ⟶ u.1.A) (hgE₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) u.1 E₀ gE₀)
    (gA₀ : A₀'.A ⟶ A.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) A A₀' gA₀)
    (φ₀ : E₀.A ⟶ A₀'.A) (φ₀' : A₀'.A ⟶ E₀.A) (hφ₀ : φ₀ ≫ A₀'.f = E₀.f)
    (hp₀ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀' φ₀ φ₀') (hl₀ : FakeEllipticCurve.PreservesLevel E₀ A₀' φ₀ hφ₀)

    (E₁ A₁ : FakeEllipticCurve Λ N S') (gE₁ : E₁.A ⟶ u'.1.A) (hgE₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S' S') u'.1 E₁ gE₁)
    (gA₁ : A₁.A ⟶ A'.A) (hgA₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S' S') A' A₁ gA₁)
    (hE : E₁.A ⟶ E₀.A) (hhE : FakeEllipticCurve.IsPullbackVia (algebraMap S S') E₀ E₁ hE)
    (hA₁ : A₁.A ⟶ A₀'.A) (hhA₁ : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A₀' A₁ hA₁)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 E₁ (gE₁ ≫ g))
    (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A₁ (gA₁ ≫ hA))
    (hsqE : hE ≫ gE₀ = gE₁ ≫ g) (hsqA : hA₁ ≫ gA₀ = gA₁ ≫ hA)
    (φ : E₁.A ⟶ A₁.A) (φ' : A₁.A ⟶ E₁.A) (hφ : φ ≫ A₁.f = E₁.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₁ A₁ φ φ') (hl : FakeEllipticCurve.PreservesLevel E₁ A₁ φ hφ)
    (hφE : φ ≫ hA₁ = hE ≫ φ₀) (hφA : φ' ≫ hE = hA₁ ≫ φ₀') :
    (pt' S' E₁ A₁ gE₁ hgE₁ gA₁ hgA₁ φ φ' hφ hp hl).1 ≫ κ S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX' =
      Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫
        (pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₀ φ₀' hφ₀ hp₀ hl₀).1 ≫ κ S u A gA hgA X ξ pt hX := by
  rw [kappa_pt_comp r d 𝒪 n C 𝔄 Xd κ hB3 S S' u u' g hg hP A gA hgA A' hA hhA hgA' X ξ pt hX X' ξ' pt' hX'
    E₁ A₁ gE₁ hgE₁ gA₁ hgA₁ hgE hgAA φ φ' hφ hp hl, ← Category.assoc]
  congr 1

  have hgE' : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 E₁ (hE ≫ gE₀) := by rw [hsqE]; exact hgE
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A₁ (hA₁ ≫ gA₀) := by rw [hsqA]; exact hgAA
  have hhE' : FakeEllipticCurve.IsPullbackVia ((IsScalarTower.toAlgHom S S S' : S →ₐ[S] S') : S →+* S') E₀ E₁ hE := by
    rwa [IsScalarTower.coe_toAlgHom]
  have hhA' : FakeEllipticCurve.IsPullbackVia ((IsScalarTower.toAlgHom S S S' : S →ₐ[S] S') : S →+* S') A₀' A₁ hA₁ := by
    rwa [IsScalarTower.coe_toAlgHom]
  have h2 := hX.2.1 S S' (IsScalarTower.toAlgHom S S S') E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₀ φ₀' hφ₀ hp₀ hl₀
    E₁ A₁ hE hhE' hA₁ hhA' hgE' hgA'' φ φ' hφ hp hl hφE hφA
  rw [IsScalarTower.coe_toAlgHom] at h2
  rw [← h2]
  exact congrArg Subtype.val (pt_congr r d pt S' E₁ A₁ _ _ hsqE.symm _ _ _ _ hsqA.symm _ _ φ φ' hφ hp hl)

theorem exists_pair_of_pt (hB2 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t))
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : IsogenyPair.PtFamily r d u.1 A ξ) (hX : IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (E₀ A₀' : FakeEllipticCurve Λ N S) (gE₀ : E₀.A ⟶ u.1.A) (hgE₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) u.1 E₀ gE₀)
    (gA₀ : A₀'.A ⟶ A.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) A A₀' gA₀)
    (x : Spec (CommRingCat.of S) ⟶ Xd)
    (hx₁ : x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)
    (hx₂ : x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Spec.map (CommRingCat.ofHom (algebraMap C S))) :
    ∃ (φ : E₀.A ⟶ A₀'.A) (φ' : A₀'.A ⟶ E₀.A) (hφ : φ ≫ A₀'.f = E₀.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀' φ φ') (hl : FakeEllipticCurve.PreservesLevel E₀ A₀' φ hφ),
      (pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ φ' hφ hp hl).1 ≫ κ S u A gA hgA X ξ pt hX = x := by
  obtain ⟨y, ⟨hy₁, hy₂⟩, -⟩ := hB2 S u A gA hgA X ξ pt hX _ x (𝟙 _)
    (by rw [Category.id_comp]; exact hx₁) (by rw [Category.id_comp]; exact hx₂)
  obtain ⟨φ, φ', hφ, hp, hl, h⟩ := hX.2.2.1 S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ ⟨y, by rw [hy₂, specMap_algebraMap_self]⟩
  exact ⟨φ, φ', hφ, hp, hl, by rw [h]; exact hy₁⟩

theorem pair_eq_of_pt_eq (hB1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)))) (hB2 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t))
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (u : FakeEllipticCurve.WithFullLevel Λ N n S)
    (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
    (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : IsogenyPair.PtFamily r d u.1 A ξ) (hX : IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (E₀ A₀' : FakeEllipticCurve Λ N S) (gE₀ : E₀.A ⟶ u.1.A) (hgE₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) u.1 E₀ gE₀)
    (gA₀ : A₀'.A ⟶ A.A) (hgA₀ : FakeEllipticCurve.IsPullbackVia (algebraMap S S) A A₀' gA₀)
    (φ₁ : E₀.A ⟶ A₀'.A) (φ₁' : A₀'.A ⟶ E₀.A) (hφ₁ : φ₁ ≫ A₀'.f = E₀.f)
    (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀' φ₁ φ₁') (hl₁ : FakeEllipticCurve.PreservesLevel E₀ A₀' φ₁ hφ₁)
    (φ₂ : E₀.A ⟶ A₀'.A) (φ₂' : A₀'.A ⟶ E₀.A) (hφ₂ : φ₂ ≫ A₀'.f = E₀.f)
    (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀' φ₂ φ₂') (hl₂ : FakeEllipticCurve.PreservesLevel E₀ A₀' φ₂ hφ₂)
    (h : (pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₁ φ₁' hφ₁ hp₁ hl₁).1 ≫ κ S u A gA hgA X ξ pt hX =
      (pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₂ φ₂' hφ₂ hp₂ hl₂).1 ≫ κ S u A gA hgA X ξ pt hX) :
    φ₁ = φ₂ ∧ φ₁' = φ₂' := by
  set P₁ := pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₁ φ₁' hφ₁ hp₁ hl₁
  set P₂ := pt S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₂ φ₂' hφ₂ hp₂ hl₂
  have hξ₁ : P₁.1 ≫ ξ = 𝟙 _ := by rw [P₁.2, specMap_algebraMap_self]
  have hξ₂ : P₂.1 ≫ ξ = 𝟙 _ := by rw [P₂.2, specMap_algebraMap_self]
  obtain ⟨hb₁, hb₂⟩ := hB1 S u A gA hgA X ξ pt hX
  obtain ⟨y, -, hy⟩ := hB2 S u A gA hgA X ξ pt hX _ (P₂.1 ≫ κ S u A gA hgA X ξ pt hX) (𝟙 _)
    (by rw [Category.assoc, hb₁, ← Category.assoc, hξ₂]) (by rw [Category.assoc, hb₂, ← Category.assoc, hξ₂])
  have e₁ : P₁.1 = y := hy P₁.1 ⟨h, hξ₁⟩
  have e₂ : P₂.1 = y := hy P₂.1 ⟨rfl, hξ₂⟩
  exact hX.2.2.2 S E₀ A₀' gE₀ hgE₀ gA₀ hgA₀ φ₁ φ₁' hφ₁ hp₁ hl₁ φ₂ φ₂' hφ₂ hp₂ hl₂ (Subtype.ext (e₁.trans e₂.symm))

end

section LayerB

open CerednikDrinfeld.QM.FakeEllipticCurve

def qmapO {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T') :
    (T ⧸ Ideal.span {algebraMap 𝒪 T π}) →+* (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) :=
  Ideal.quotientMap (Ideal.span {algebraMap 𝒪 T' π}) ((φ.restrictScalars 𝒪 : T →ₐ[𝒪] T') : T →+* T')
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show ((φ.restrictScalars 𝒪 : T →ₐ[𝒪] T') : T →+* T') (algebraMap 𝒪 T π) = algebraMap 𝒪 T' π from
            (φ.restrictScalars 𝒪).commutes π]
          exact Ideal.subset_span rfl))))

theorem qmapO_comp_mk {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T') :
    (qmapO π φ).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : T →+* T') := by
  ext x; rfl

def qmapC {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T') :
    (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) →+* (T' ⧸ Ideal.span {algebraMap C T' (algebraMap 𝒪 C π)}) :=
  Ideal.quotientMap _ (φ : T →+* T')
    (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, AlgHom.coe_toRingHom, AlgHom.commutes]
        exact Ideal.subset_span rfl)

theorem eqq_qmap {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T') :
    (RelRepS14.eqq π C T').symm.toRingHom.comp (qmapO π φ) = (qmapC π φ).comp (RelRepS14.eqq π C T).symm.toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

theorem isoVia_refl {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsoVia E E (Iso.refl E.A) (by simp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    simp only [mapPt_coe, Iso.refl_hom, Category.comp_id]
    exact mul_val_congr E.L rfl _ _ _ _ (by simp [mapPt_coe]) (by simp [mapPt_coe])
  · intro x; simp
  · intro T t P
    have : mapPt (Iso.refl E.A).hom (by simp) P = P := Subtype.ext (by simp [mapPt_coe])
    rw [this]

theorem xPt_natural
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (hB3 : (∀ (d : ℕ), ∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
    (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
    (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ') :
    ∃ hd : ρ'.d = ρ.d,
      RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' ≫ eqToHom (congrArg Xbar hd) =
        Spec.map (CommRingCat.ofHom (qmapC π φ)) ≫ RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ := by

  obtain ⟨Eb', gb', hEb', Ab', gAb', hAb', d', φ₁, φ₁', hφ₁, hp₁, hl₁⟩ := ρ'
  obtain ⟨ub, uA, hub, hubg, huA, huAg, hd, hφφ⟩ := hρ
  change d' = ρ.d at hd
  subst hd
  refine ⟨rfl, ?_⟩
  rw [eqToHom_refl, Category.comp_id]

  letI iT : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.algq π C T
  haveI : IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.tower π C T
  letI iT' : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) := RelRepS14.algq π C T'
  haveI : IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) := RelRepS14.tower π C T'
  letI iTT : Algebra (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) := (qmapO π φ).toAlgebra
  have halg : algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) = qmapO π φ := rfl
  haveI : IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) := IsScalarTower.of_algebraMap_eq' (by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change Ideal.Quotient.mk _ (algebraMap C T' x) = Ideal.Quotient.mk _ ((φ : T →+* T') (algebraMap C T x))
    rw [AlgHom.coe_toRingHom, AlgHom.commutes])
  haveI : IsScalarTower 𝒪 (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change Ideal.Quotient.mk _ (algebraMap 𝒪 T' x) = Ideal.Quotient.mk _ ((φ.restrictScalars 𝒪 : T →ₐ[𝒪] T') (algebraMap 𝒪 T x))
    rw [AlgHom.commutes])
  have htow : (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})).comp (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) = algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) :=
    (IsScalarTower.algebraMap_eq _ _ _).symm

  obtain ⟨gf, hgf₁, hgf₂⟩ := RelRepS14.exists_factor (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) (qmapO π φ)
      ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T' π})).comp (φ : T →+* T')) (qmapO_comp_mk π φ)
      u.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) ≫ g)
      (IsPullbackVia.comp (φ : T →+* T') (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T' π})) u.1 u'.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1 g
        (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) hg (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1)

  have hPf : ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2.P).1 ≫ gf = Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}))) ≫ ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).1 := by
    obtain ⟨⟨hsq, -, -, -⟩, hgenT⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ
    obtain ⟨-, hgenT'⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
    obtain ⟨hsqf, -, -, -⟩ := hgf₂
    apply hsq.hom_ext
    · simp only [Category.assoc]
      rw [hgf₁, reassoc_of% hgenT', hP, hgenT, ← Category.assoc, ← Category.assoc, ← RelRepS14.specMap_comp, ← RelRepS14.specMap_comp, halg,
        qmapO_comp_mk]
    · simp only [Category.assoc]
      rw [hsqf.w, reassoc_of% ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2.P).2, ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).2, halg]
      simp

  have hgAeq : RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) = uA ≫ RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ := by
    obtain ⟨hsq𝔄, -, -, -⟩ := id h𝔄
    obtain ⟨hsq1, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2
    obtain ⟨hsq2, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    obtain ⟨hsq3, -, -, -⟩ := huA
    apply hsq𝔄.hom_ext
    · rw [(RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1, Category.assoc, (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1]
      exact huAg.symm
    · rw [hsq1.w, Category.assoc, hsq2.w, ← Category.assoc, hsq3.w, Category.assoc, ← RelRepS14.specMap_comp]
      change _ = _ ≫ Spec.map (CommRingCat.ofHom ((algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})).comp (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}))))
      rw [htow]
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})) 𝔄 Ab' (uA ≫ RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := by
    rw [← hgAeq]; exact (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2

  obtain ⟨ψ₁, ψ₁', hψ₁, hq₁, hm₁, hψ₁E, hψ₁A⟩ := exists_pullPair (qmapO π φ) (r ^ ρ.d) ρ.Eb ρ.Ab Eb' Ab' ub hub uA huA
    ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel
  have hψφ : ψ₁ = φ₁ := by
    obtain ⟨hsqA, -, -, -⟩ := huA
    apply hsqA.hom_ext
    · rw [hψ₁E]; exact hφφ
    · rw [hψ₁]; exact hφ₁.symm

  have hsqE : ub ≫ RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ = RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) ≫ gf := by
    obtain ⟨⟨hsq, -, -, -⟩, -⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ
    obtain ⟨hsqf, -, -, -⟩ := hgf₂
    obtain ⟨hsqb, -, -, -⟩ := hub
    obtain ⟨hsqe, -, -, -⟩ := (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    obtain ⟨hsqe', -, -, -⟩ := (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2
    apply hsq.hom_ext
    · simp only [Category.assoc]
      rw [(RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1, hgf₁, reassoc_of% (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1]
      exact hubg
    · simp only [Category.assoc]
      rw [hsqe.w, reassoc_of% hsqb.w, hsqf.w, reassoc_of% hsqe'.w, RelRepS14.specMap_id, RelRepS14.specMap_id]
      simp only [Category.comp_id, Category.id_comp]
      rfl
  have hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 Eb' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) ≫ gf) := by
    have := IsPullbackVia.comp (qmapO π φ) (RingHom.id _) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1 Eb' gf (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) hgf₂ (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2
    rwa [RingHom.id_comp] at this
  have hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})) ρ.Ab Ab' (𝟙 _ ≫ uA) := by
    rw [Category.id_comp]; exact huA

  unfold RelRepS14.xPt
  rw [← Category.assoc (Spec.map _) (Spec.map _), ← RelRepS14.specMap_comp, ← eqq_qmap, RelRepS14.specMap_comp, Category.assoc]
  congr 1

  have step3 := kappa_pt_natural r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (hB3 ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π})
      (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) gf hgf₂ hPf ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 Ab' uA huA hgA''
      (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1))
      ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ.Ab)
      ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel
      Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab')
      ub hub uA huA hgE hgAA hsqE (by simp) ψ₁ ψ₁' hψ₁ hq₁ hm₁ hψ₁E hψ₁A
  have step2 : RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2 (𝟙 _)
        (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab') φ₁ φ₁' hφ₁ hp₁ hl₁ =
      RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2 (𝟙 _)
        (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab') ψ₁ ψ₁' hψ₁ hq₁ hm₁ :=
    (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).1 (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) Eb' Ab' _ _ _ _ φ₁ φ₁' hφ₁ hp₁ hl₁
      Eb' Ab' _ _ _ _ ψ₁ ψ₁' hψ₁ hq₁ hm₁ (Iso.refl _) (by simp) (Iso.refl _) (by simp) (isoVia_refl _) (isoVia_refl _)
      (by simp) (by simp) (by rw [hψφ]; simp)
  unfold RelRepS14.x0 RelRepS14.p0
  rw [kappa_congr r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)) Ab' _ _ hgAeq (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)).2 hgA'',
    step2, step3]

noncomputable def uq0 {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (n : ℕ) (T : Type) [CommRing T] [Algebra 𝒪 T]
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) : FakeEllipticCurve.WithFullLevel Λ N n (T ⧸ Ideal.span {algebraMap 𝒪 T π}) :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose

noncomputable def gu0 {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (n : ℕ) (T : Type) [CommRing T] [Algebra 𝒪 T]
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) : (uq0 π n T u).1.A ⟶ u.1.A :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose_spec.choose

theorem gu0_spec {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (n : ℕ) (T : Type) [CommRing T] [Algebra 𝒪 T]
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) :
    FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (uq0 π n T u).1 (gu0 π n T u) ∧
    FakeEllipticCurve.WithFullLevel.IsPullback (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u (uq0 π n T u) := by
  obtain ⟨hg, hmul, hact, hlev, -, hgen⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose_spec.choose_spec
  exact ⟨⟨hg, hmul, hact, hlev⟩, ⟨gu0 π n T u, hg, hmul, hact, hlev, hgen⟩⟩

theorem specMap_eqq_symm_eqq {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] :
    Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom) =
      𝟙 _ := by
  rw [← RelRepS14.specMap_comp]
  have : (RelRepS14.eqq π C T).symm.toRingHom.comp (RelRepS14.eqq π C T).toRingHom = RingHom.id _ := by
    ext x; simp
  rw [this]
  exact RelRepS14.specMap_id _

theorem eqq_comp_mk {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] :
    (RelRepS14.eqq π C T).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) := by
  ext x; rfl

theorem x0_surj
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (hB2 : (∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t))
    (hB3 : (∀ (d : ℕ), ∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (y : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap 𝒪 T π})) ⟶ Xbar d)
    (hy₁ : y ≫ qbar d ≫ pullback.fst fM _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)
    (hy₂ : y ≫ qbar d ≫ pullback.snd fM _ = Spec.map (CommRingCat.ofHom (RelRepS14.qmap π C T))) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
      RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ eqToHom (congrArg Xbar hd) = y := by
  letI iT : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.algq π C T
  haveI : IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.tower π C T
  obtain ⟨hgu₀, huq₀⟩ := gu0_spec π n T u
  obtain ⟨hg0, -, -, -⟩ := id hgu₀
  obtain ⟨Ab₀, gAb₀, hsqA, hmulA, hactA, hlevA, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) 𝔄
  have hAb₀ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) 𝔄 Ab₀ gAb₀ := ⟨hsqA, hmulA, hactA, hlevA⟩
  have hleg : (RelRepS14.qmap π C T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) =
      FakeEllipticCurve.Rigidification.residueLeg π ψT := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change ((RelRepS14.qmap π C T).comp (Ideal.Quotient.mk _)) ((ψ : Onr →+* C) x) = Ideal.Quotient.mk _ ((ψT : Onr →+* T) x)
    rw [RelRepS14.qmap_comp_mk, RingHom.comp_apply, hψT]
    rfl
  have hAbψ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψT) A₀ Ab₀ (gAb₀ ≫ g𝔄) := by
    rw [← hleg]
    exact IsPullbackVia.comp _ _ A₀ 𝔄 Ab₀ g𝔄 gAb₀ h𝔄 hAb₀
  obtain ⟨X₀, ξ₀, -, pt₀, hX₀⟩ := hloc d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq0 π n T u) Ab₀ gAb₀ hAb₀
  have hy₁' : y ≫ qbar d ≫ pullback.fst fM _ = (ptF (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (T ⧸ Ideal.span {algebraMap 𝒪 T π})))) (uq0 π n T u)).1 := by
    rw [hy₁]
    exact (hM.ptF_pullback T _ (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) _ _ (by rw [← RelRepS14.specMap_comp]) u _ huq₀).symm
  obtain ⟨φ, φ', hφ, hp, hl, hpt⟩ := exists_pair_of_pt r d 𝒪 n M fM ptF (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar d) (qbar d) (κ d) (hB2 d)
    (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq0 π n T u) Ab₀ gAb₀ hAb₀ X₀ ξ₀ pt₀ hX₀ (uq0 π n T u).1 Ab₀ (𝟙 (uq0 π n T u).1.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
    (𝟙 Ab₀.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _) y hy₁' hy₂
  refine ⟨(⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1), rfl, ?_⟩
  simp only [eqToHom_refl, Category.comp_id]
  have hgAeq : RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) = 𝟙 Ab₀.A ≫ gAb₀ := by
    obtain ⟨hsq𝔄, -, -, -⟩ := id h𝔄
    obtain ⟨hsq1, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).2
    apply hsq𝔄.hom_ext
    · rw [(RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).1, Category.id_comp]
    · rw [hsq1.w, Category.id_comp, hsqA.w]
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) 𝔄 Ab₀ (𝟙 Ab₀.A ≫ gAb₀) := by
    rw [Category.id_comp]; exact hAb₀
  have hgEeq : (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : (uq0 π n T u).1.A ⟶ (uq0 π n T u).1.A) ≫ 𝟙 (uq0 π n T u).1.A = 𝟙 (uq0 π n T u).1.A := by
    obtain ⟨hsqe, -, -, -⟩ := (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).2
    refine (Category.comp_id _).trans ?_
    apply hg0.hom_ext
    · rw [Category.id_comp]; exact (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).1
    · rw [Category.id_comp]
      refine hsqe.w.trans ?_
      rw [RelRepS14.specMap_id]
      erw [Category.comp_id]
  have hP0 : ((uq0 π n T u).2.P).1 ≫ 𝟙 (uq0 π n T u).1.A = Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) ≫ ((uq0 π n T u).2.P).1 := by
    rw [Category.comp_id, specMap_algebraMap_self, Category.id_comp]
  have hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (uq0 π n T u).1 (uq0 π n T u).1 ((RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : (uq0 π n T u).1.A ⟶ (uq0 π n T u).1.A) ≫ 𝟙 (uq0 π n T u).1.A) := by
    rw [hgEeq]; exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _
  have hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) Ab₀ Ab₀ (𝟙 Ab₀.A ≫ 𝟙 Ab₀.A) := by
    rw [Category.id_comp]; exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _
  have step1 := kappa_pt_comp r d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar d) (κ d) (hB3 d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})
      (uq0 π n T u) (uq0 π n T u) (𝟙 (uq0 π n T u).1.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _) hP0
      Ab₀ gAb₀ hAb₀ Ab₀ (𝟙 Ab₀.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _) hgA''
      X₀ ξ₀ pt₀ hX₀ (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1))
      (uq0 π n T u).1 Ab₀ (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : (uq0 π n T u).1.A ⟶ (uq0 π n T u).1.A) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).2 (𝟙 Ab₀.A)
      (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _) hgE hgAA φ φ' hφ hp hl
  unfold RelRepS14.x0
  have e1 : (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).1 ≫ κ d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) Ab₀ (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) =
      (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).1 ≫ κ d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) Ab₀ (𝟙 Ab₀.A ≫ gAb₀) hgA'' (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) :=
    congrArg (fun k => (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).1 ≫ k)
      (kappa_congr r d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar d) (κ d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) Ab₀ _ _ hgAeq
        (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)).2 hgA'' (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u (⟨(uq0 π n T u).1, (gu0 π n T u), hgu₀, Ab₀, gAb₀ ≫ g𝔄, hAbψ, d, φ, φ', hφ, hp, hl⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)))
  have e3 := congrArg (fun P => P.1 ≫ κ d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq0 π n T u) Ab₀ gAb₀ hAb₀ X₀ ξ₀ pt₀ hX₀)
    (pt_congr r d pt₀ (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (uq0 π n T u).1 Ab₀ _ _ hgEeq hgE (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
      _ _ (Category.id_comp _) hgAA (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _) φ φ' hφ hp hl)
  exact e1.trans (step1.trans (e3.trans hpt))

theorem xPt_surj
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (hB2 : (∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t))
    (hB3 : (∀ (d : ℕ), ∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T)
    (xb : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ Xbar d)
    (hxb₁ : xb ≫ qbar d ≫ pullback.fst fM _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)
    (hxb₂ : xb ≫ qbar d ≫ pullback.snd fM _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C T))) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
      RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ eqToHom (congrArg Xbar hd) = xb := by
  have hy₁ : ((Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom) ≫ xb)) ≫ qbar d ≫ pullback.fst fM _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 := by
    rw [Category.assoc, hxb₁, ← Category.assoc, ← RelRepS14.specMap_comp, eqq_comp_mk]
  have hy₂ : ((Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom) ≫ xb)) ≫ qbar d ≫ pullback.snd fM _ = Spec.map (CommRingCat.ofHom (RelRepS14.qmap π C T)) := by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))]
    simp only [Category.assoc]
    rw [hxb₂, ← Category.assoc, ← RelRepS14.specMap_comp, eqq_comp_mk, ← RelRepS14.specMap_comp, ← RelRepS14.specMap_comp,
      RelRepS14.qmap_comp_mk]
  obtain ⟨ρ, hd, h⟩ := x0_surj r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc hB2 hB3 d T ψT hψT u ((Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom) ≫ xb)) hy₁ hy₂
  refine ⟨ρ, hd, ?_⟩
  unfold RelRepS14.xPt
  rw [Category.assoc, h, ← Category.assoc, specMap_eqq_symm_eqq, Category.id_comp]

theorem x0_eq_of_iso
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (hB3 : (∀ (d : ℕ), ∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
    (hd : ρ'.d = ρ.d)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hv : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib₁ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (hib₂ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huA' : uA ≫ ρ.gA = ρ'.gA)
    (hφ : ib ≫ ρ'.φ ≫ uA = ρ.φ) :
    RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' ρ' ≫ eqToHom (congrArg Xbar hd) = RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ := by
  obtain ⟨Eb', gb', hEb', Ab', gAb', hAb', d', φ₁, φ₁', hφ₁, hp₁, hl₁⟩ := ρ'
  change d' = ρ.d at hd
  subst hd
  simp only [eqToHom_refl, Category.comp_id]
  change ib ≫ gb' = ρ.gb ≫ i.hom at hib₁
  change ib ≫ Eb'.f = ρ.Eb.f at hib₂
  change FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab Ab' uA at huA
  change uA ≫ ρ.gA = gAb' at huA'
  change ib ≫ φ₁ ≫ uA = ρ.φ at hφ
  letI iT : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.algq π C T
  haveI : IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.tower π C T
  obtain ⟨hvm, hva, hvl, hvP⟩ := hv
  have hvE : FakeEllipticCurve.IsoVia u.1 u'.1 i hi := ⟨hvm, hva, hvl⟩
  have hi_inv : FakeEllipticCurve.IsPullbackVia (RingHom.id T) u.1 u'.1 i.inv :=
    Alg5X4.isPullbackVia_id_of_isoVia_inv u.1 u'.1 i hi hvE
  have hi_hom : FakeEllipticCurve.IsPullbackVia (RingHom.id T) u'.1 u.1 i.hom :=
    Alg5X4.isPullbackVia_id_of_isoVia u.1 u'.1 i hi hvE
  have hgen : (u'.2.P).1 = (u.2.P).1 ≫ i.hom := by rw [← hvP, mapPt_coe]

  have hcomp' : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 ((RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) ≫ i.inv) := by
    have := IsPullbackVia.comp (RingHom.id T) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 u'.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 i.inv (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) hi_inv (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1
    rwa [RingHom.comp_id] at this
  obtain ⟨gq, hgq₁, hgq₂⟩ := RelRepS14.exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1
    ((RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) ≫ i.inv) hcomp'
  have hPq : ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2.P).1 ≫ gq = Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) ≫ ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).1 := by
    obtain ⟨⟨hsq, -, -, -⟩, hgenP⟩ := (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)
    obtain ⟨-, hgenQ⟩ := (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1))
    obtain ⟨hsqq, -, -, -⟩ := hgq₂
    apply hsq.hom_ext
    · simp only [Category.assoc]
      rw [hgq₁, reassoc_of% hgenQ, hgenP, hgen, Category.assoc, Iso.hom_inv_id, Category.comp_id, specMap_algebraMap_self,
        Category.id_comp]
    · simp only [Category.assoc]
      rw [hsqq.w, reassoc_of% ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2.P).2, ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).2, specMap_algebraMap_self]
      simp

  have hgAeq : (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) = uA ≫ (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := by
    obtain ⟨hsq𝔄, -, -, -⟩ := id h𝔄
    obtain ⟨hsq1, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
    obtain ⟨hsq2, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    obtain ⟨hsq3, -, -, -⟩ := id huA
    apply hsq𝔄.hom_ext
    · rw [(RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1, Category.assoc, (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1]
      exact huA'.symm
    · rw [hsq1.w, Category.assoc, hsq2.w, ← Category.assoc, hsq3.w, RelRepS14.specMap_id, Category.comp_id]
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) 𝔄 Ab' (uA ≫ (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)) := by
    rw [← hgAeq]; exact (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2

  have hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 Eb' ((RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) ≫ gq) := by
    have := IsPullbackVia.comp (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 Eb' gq (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) hgq₂ (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
    rwa [RingHom.comp_id] at this
  have hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) ρ.Ab Ab' (𝟙 Ab'.A ≫ uA) := by
    rw [Category.id_comp]; exact huA
  have step1 := kappa_pt_comp r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (hB3 ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})
      (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) gq hgq₂ hPq ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 Ab' uA huA hgA''
      (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1))
      Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (𝟙 Ab'.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
      hgE hgAA φ₁ φ₁' hφ₁ hp₁ hl₁

  have hcompE : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 ρ.Eb (ρ.gb ≫ i.hom) := by
    have := IsPullbackVia.comp (RingHom.id T) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 u.1 ρ.Eb i.hom ρ.gb hi_hom ρ.isPullback_Eb
    rwa [RingHom.comp_id] at this
  obtain ⟨kb, hkb₁, hkb₂⟩ := RelRepS14.exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 Eb' ρ.Eb gb' hEb' (ρ.gb ≫ i.hom) hcompE
  obtain ⟨kb', hkb'₁, hkb'₂⟩ := RelRepS14.exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 ρ.Eb Eb' (ρ.gb ≫ i.hom) hcompE gb' hEb'
  obtain ⟨vA, hvA₁, hvA₂⟩ := RelRepS14.exists_comparison (FakeEllipticCurve.Rigidification.residueLeg π ψT) A₀ Ab' ρ.Ab gAb' hAb'
    ρ.gA ρ.isPullback_Ab
  have hkbf := Alg5X4.over_of_isPullbackVia_id _ _ kb hkb₂
  have hkb'f := Alg5X4.over_of_isPullbackVia_id _ _ kb' hkb'₂
  have hvAf := Alg5X4.over_of_isPullbackVia_id _ _ vA hvA₂
  have huAf := Alg5X4.over_of_isPullbackVia_id _ _ uA huA
  have hibk : ib = kb := by
    obtain ⟨hsqb', -, -, -⟩ := id hEb'
    apply hsqb'.hom_ext
    · rw [hkb₁]; exact hib₁
    · rw [hkbf]; exact hib₂
  obtain ⟨hsqEc, -, -, -⟩ := id hcompE
  obtain ⟨hsqEb', -, -, -⟩ := id hEb'
  obtain ⟨hsqAρ, -, -, -⟩ := id ρ.isPullback_Ab
  obtain ⟨hsqAb', -, -, -⟩ := id hAb'
  have hE₁ : kb ≫ kb' = 𝟙 _ :=
    Alg5X4.comp_eq_id_of_comparisons _ u'.1 ρ.Eb Eb' (ρ.gb ≫ i.hom) hsqEc gb' kb' hkb'₁ hkb'f kb hkb₁ hkbf
  have hE₂ : kb' ≫ kb = 𝟙 _ :=
    Alg5X4.comp_eq_id_of_comparisons _ u'.1 Eb' ρ.Eb gb' hsqEb' (ρ.gb ≫ i.hom) kb hkb₁ hkbf kb' hkb'₁ hkb'f
  have hA₁ : vA ≫ uA = 𝟙 _ :=
    Alg5X4.comp_eq_id_of_comparisons _ A₀ ρ.Ab Ab' ρ.gA hsqAρ gAb' uA huA' huAf vA hvA₁ hvAf
  have hA₂ : uA ≫ vA = 𝟙 _ :=
    Alg5X4.comp_eq_id_of_comparisons _ A₀ Ab' ρ.Ab gAb' hsqAb' ρ.gA vA hvA₁ hvAf uA huA' huAf
  have hvEiso : FakeEllipticCurve.IsoVia Eb' ρ.Eb ⟨kb', kb, hE₂, hE₁⟩ hkb'f :=
    Alg5X4.isoVia_of_isPullbackVia_id Eb' ρ.Eb kb' kb hkb'₂ hkb₂ hE₂ hE₁ hkb'f
  have hvAiso : FakeEllipticCurve.IsoVia Ab' ρ.Ab ⟨uA, vA, hA₂, hA₁⟩ huAf :=
    Alg5X4.isoVia_of_isPullbackVia_id Ab' ρ.Ab uA vA huA hvA₂ hA₂ hA₁ huAf

  obtain ⟨ψ₁, ψ₁', hψ₁, hq₁, hm₁, hψ₁E, hψ₁A⟩ :=
    exists_pullPair (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (r ^ ρ.d) Eb' Ab' ρ.Eb ρ.Ab kb hkb₂ vA hvA₂ φ₁ φ₁' hφ₁ hp₁ hl₁
  have hφ' : kb ≫ φ₁ ≫ uA = ρ.φ := by rw [← hibk]; exact hφ
  have hψρ : ψ₁ = ρ.φ := by
    rw [← hφ', ← Category.assoc, ← hψ₁E, Category.assoc, hA₁, Category.comp_id]

  have hgEcmp : kb' ≫ (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) = (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) ≫ gq := by
    obtain ⟨⟨hsq, -, -, -⟩, -⟩ := (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)
    obtain ⟨hsqe, -, -, -⟩ := (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    obtain ⟨hsqe', -, -, -⟩ := (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
    obtain ⟨hsqq, -, -, -⟩ := hgq₂
    apply hsq.hom_ext
    · simp only [Category.assoc]
      rw [(RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1, hgq₁, reassoc_of% (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1, Iso.eq_comp_inv, Category.assoc]
      exact hkb'₁
    · simp only [Category.assoc]
      rw [hsqe.w, reassoc_of% hkb'f, hsqq.w, reassoc_of% hsqe'.w, RelRepS14.specMap_id]
      simp
  have hX1c : kb' ≫ ψ₁ = φ₁ ≫ uA := by
    rw [hψρ, ← hφ', ← Category.assoc, hE₂, Category.id_comp]
  have step2 := (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (T ⧸ Ideal.span {algebraMap 𝒪 T π}) Eb' Ab' ((RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) ≫ gq) hgE (𝟙 Ab'.A ≫ uA) hgAA φ₁ φ₁' hφ₁ hp₁ hl₁
      ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 ρ.Ab.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
      ψ₁ ψ₁' hψ₁ hq₁ hm₁ ⟨kb', kb, hE₂, hE₁⟩ hkb'f ⟨uA, vA, hA₂, hA₁⟩ huAf hvEiso hvAiso hgEcmp (by simp) hX1c
  have step3 := (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (T ⧸ Ideal.span {algebraMap 𝒪 T π}) ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 ρ.Ab.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
      ψ₁ ψ₁' hψ₁ hq₁ hm₁
      ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 ρ.Ab.A) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ _)
      ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel
      (Iso.refl _) (by simp) (Iso.refl _) (by simp) (isoVia_refl _) (isoVia_refl _) (by simp) (by simp) (by rw [hψρ]; simp)

  unfold RelRepS14.x0
  have e1 : (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) Ab' (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) =
      (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) Ab' (uA ≫ (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)) hgA'' (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) :=
    congrArg (fun k => (RelRepS14.p0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 ≫ k)
      (kappa_congr r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) Ab' _ _ hgAeq (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 hgA''
        (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)))
  have e23 := congrArg (fun P => P.1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ))
    (step2.trans step3)
  exact e1.trans (step1.trans e23)

end LayerB

end RelRepX

namespace Alg5X4

open CerednikDrinfeld.QM.FakeEllipticCurve RelRepX

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem iso_of_x0_eq
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (hB2 : (∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t))
    (hB3 : (∀ (d : ℕ), ∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
    (hd : ρ'.d = ρ.d)
    (h : RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' ρ' ≫ eqToHom (congrArg Xbar hd) =
      RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) :
    ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
      ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
        ib ≫ ρ'.φ ≫ uA = ρ.φ := by

  obtain ⟨Eb', gb', hEb', Ab', gAb', hAb', d', φ₁, φ₁', hφ₁, hp₁, hl₁⟩ := ρ'
  cases hd
  simp only [eqToHom_refl, Category.comp_id] at h

  letI iT : Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.algq π C T
  haveI iTt : IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) := RelRepS14.tower π C T

  have hπT : algebraMap 𝒪 T π = 0 := by rw [IsScalarTower.algebraMap_apply 𝒪 C T]; exact h0
  haveI hmkIso : IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})))) := isIso_specMap_quotient_mk_of_eq_zero _ hπT
  have hfst : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u').1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 :=
    (RelRepS14.x0_fst r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).symm.trans
      ((congrArg (fun x => x ≫ qbar ρ.d ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}))))) h).trans
        (RelRepS14.x0_fst r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ))
  have hptF : ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u = ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u' :=
    (Subtype.ext ((cancel_epi _).1 hfst)).symm
  obtain ⟨i, hi, hv⟩ := hM.ptF_injective T _ u u' hptF
  have hvE : FakeEllipticCurve.IsoVia u.1 u'.1 i hi := ⟨hv.1, hv.2.1, hv.2.2.1⟩
  have hP : (u.2.P).1 ≫ i.hom = (u'.2.P).1 := by
    have := congrArg Subtype.val hv.2.2.2; simpa only [mapPt_coe] using this
  have hH1 : FakeEllipticCurve.IsPullbackVia (RingHom.id T) u'.1 u.1 i.hom := isPullbackVia_id_of_isoVia u.1 u'.1 i hi hvE
  have hH1' : FakeEllipticCurve.IsPullbackVia (RingHom.id T) u.1 u'.1 i.inv := isPullbackVia_id_of_isoVia_inv u.1 u'.1 i hi hvE

  have hρEb : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 ρ.Eb (ρ.gb ≫ i.hom) := by
    have := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (RingHom.id T) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 u.1 ρ.Eb i.hom ρ.gb hH1 ρ.isPullback_Eb
    rwa [RingHom.comp_id] at this
  obtain ⟨ib, hib₁, hibP⟩ := RelRepS14.exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u'.1 Eb' ρ.Eb gb' hEb' (ρ.gb ≫ i.hom) hρEb
  have hib₂ : ib ≫ Eb'.f = ρ.Eb.f := over_of_isPullbackVia_id Eb' ρ.Eb ib hibP
  obtain ⟨iE, hiE, hiEhom, hvIE⟩ := iso_of_isPullbackVia_id Eb' ρ.Eb ib hibP
  obtain ⟨uA, huAg, huA⟩ := RelRepS14.exists_comparison _ A₀ ρ.Ab Ab' ρ.gA ρ.isPullback_Ab gAb' hAb'
  obtain ⟨iA', hiA', hiA'hom, hvIA'⟩ := iso_of_isPullbackVia_id ρ.Ab Ab' uA huA
  obtain ⟨hiA'', hvIA⟩ := isoVia_symm' Ab' ρ.Ab iA' hiA' hvIA'
  have hPA : FakeEllipticCurve.IsPullbackVia (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) Ab' ρ.Ab iA'.inv :=
    isPullbackVia_id_of_isoVia_inv Ab' ρ.Ab iA' hiA' hvIA'
  have huq' : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ i.inv) := by
    have := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (RingHom.id T) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 u'.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 i.inv (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) hH1' (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1
    rwa [RingHom.comp_id] at this
  obtain ⟨g, hg₁, hgP⟩ := RelRepS14.exists_comparison (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u.1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.gu r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ i.inv) huq'
  have hgf : g ≫ (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1.f = (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1.f := over_of_isPullbackVia_id _ _ g hgP
  have hPg : ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}))) ≫ ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).1 := by
    obtain ⟨⟨hsq, -, -, -⟩, hgen⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ
    obtain ⟨-, hgen'⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
    rw [RelRepX.specMap_algebraMap_self, Category.id_comp]
    apply hsq.hom_ext
    · rw [Category.assoc, hg₁, ← Category.assoc, hgen', hgen, Category.assoc, ← hP, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [Category.assoc, hgf, ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2.P).2, ((RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2.P).2]
  have hgAeq : RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) = uA ≫ RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ := by
    obtain ⟨hsq𝔄, -, -, -⟩ := id h𝔄
    obtain ⟨hsq1, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
    obtain ⟨hsq2, -, -, -⟩ := (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
    obtain ⟨hsq3, -, -, -⟩ := huA
    apply hsq𝔄.hom_ext
    · rw [(RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1, Category.assoc, (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1]; exact huAg.symm
    · rw [hsq1.w, Category.assoc, hsq2.w, ← Category.assoc, hsq3.w, specMap_ofHom_id, Category.comp_id]
  have hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) 𝔄 Ab' (uA ≫ RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := by
    rw [← hgAeq]; exact (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
  have hgE : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 Eb' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ g) := by
    have := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1 Eb' g (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) hgP (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
    rwa [RingHom.comp_id] at this
  have hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π})) ρ.Ab Ab' (𝟙 _ ≫ uA) := by
    rw [Category.id_comp]; exact huA

  obtain ⟨ψ₁, ψ₁', hψ₁, hq₁, hm₁, hψ₁A, hψ₁E⟩ := RelRepX.exists_pullPair (RingHom.id (T ⧸ Ideal.span {algebraMap 𝒪 T π})) (r ^ ρ.d) Eb' Ab' ρ.Eb ρ.Ab ib hibP iA'.inv hPA φ₁ φ₁' hφ₁ hp₁ hl₁

  have step1 := RelRepX.kappa_pt_comp r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (hB3 ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) g hgP hPg
    ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 Ab' uA huA hgA'' (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1))
    Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab') hgE hgAA φ₁ φ₁' hφ₁ hp₁ hl₁
  have hgEo1 : RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ≫ (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1.f = ρ.Eb.f := over_of_isPullbackVia_id _ _ _ (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2
  have hgEo2 : RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1.f = Eb'.f := over_of_isPullbackVia_id _ _ _ (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2
  have hgEc : iE.hom ≫ (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ g) = RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ := by
    obtain ⟨⟨hsq, -, -, -⟩, -⟩ := RelRepS14.gu_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ
    rw [hiEhom]
    apply hsq.hom_ext
    · simp only [Category.assoc]
      rw [hg₁, reassoc_of% (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).1, reassoc_of% hib₁, Iso.hom_inv_id, Category.comp_id, (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1]
    · simp only [Category.assoc]
      rw [hgf, hgEo2, hib₂, hgEo1]
  have step2 := (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).1 (T ⧸ Ideal.span {algebraMap 𝒪 T π}) ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ.Ab) ψ₁ ψ₁' hψ₁ hq₁ hm₁
    Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) ≫ g) hgE (𝟙 _ ≫ uA) hgAA φ₁ φ₁' hφ₁ hp₁ hl₁ iE hiE iA'.symm hiA'' hvIE hvIA hgEc
    (by rw [Iso.symm_hom, Category.id_comp, ← hiA'hom, Iso.inv_hom_id]) (by rw [hiEhom, Iso.symm_hom]; exact hψ₁A.symm)

  have e1 : RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ =
      (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ (T ⧸ Ideal.span {algebraMap 𝒪 T π}) ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ.Ab) ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel).1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) := rfl
  have e2 : RelRepS14.x0 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) =
      (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab') φ₁ φ₁' hφ₁ hp₁ hl₁).1 ≫
        κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) Ab' (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) := rfl
  have kc := congrArg (fun k => (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) Eb' Ab' (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ Ab') φ₁ φ₁' hφ₁ hp₁ hl₁).1 ≫ k)
    (RelRepX.kappa_congr r ρ.d 𝒪 n (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (κ ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) Ab' (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (uA ≫ RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) hgAeq (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)).2 hgA'' (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u' (⟨Eb', gb', hEb', Ab', gAb', hAb', ρ.d, φ₁, φ₁', hφ₁, hp₁, hl₁⟩ : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)))
  have key := e1.symm.trans (h.symm.trans (e2.trans (kc.trans (step1.trans (congrArg (fun p => p.1 ≫ κ ρ.d (T ⧸ Ideal.span {algebraMap 𝒪 T π}) (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ)) step2).symm))))
  obtain ⟨hφψ, -⟩ := RelRepX.pair_eq_of_pt_eq r ρ.d 𝒪 n M fM ptF (C ⧸ Ideal.span {algebraMap 𝒪 C π}) 𝔄 (Xbar ρ.d) (qbar ρ.d) (κ ρ.d) (hB1 ρ.d) (hB2 ρ.d) (T ⧸ Ideal.span {algebraMap 𝒪 T π})
    (RelRepS14.uq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Ab (RelRepS14.gA r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gA_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (RelRepS14.X r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.ξ r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.pt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.hX r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) ρ.Eb ρ.Ab (RelRepS14.gE r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ) (RelRepS14.gE_spec r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ).2 (𝟙 _) (CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ρ.Ab)
    ρ.φ ρ.φ' ρ.φ_over ρ.isIsogenyPair ρ.preservesLevel ψ₁ ψ₁' hψ₁ hq₁ hm₁ key
  refine ⟨i, hi, hv, ib, hib₁, hib₂, uA, huA, huAg, ?_⟩
  show ib ≫ φ₁ ≫ uA = ρ.φ
  rw [hφψ, ← hiA'hom, ← Category.assoc, ← hψ₁A, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Alg5X4

namespace RelRepX

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem qmapC_comp_mk {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T') :
    (qmapC π φ).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : T →+* T') := by
  ext x; rfl

theorem quotEquiv_comp_qmapC {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
    (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0) :
    (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0')).trans (RingEquiv.quotientBot T')).toRingHom).comp (qmapC π φ) = (φ : T →+* T').comp (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc, RingHom.comp_assoc, qmapC_comp_mk, ← RingHom.comp_assoc,
    RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T' h0', RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0,
    RingHom.id_comp, RingHom.comp_id]

theorem specMap_mk_quotEquiv {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T : Type} [CommRing T] [Algebra C T] (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) = 𝟙 _ := by
  rw [← RelRepS14.specMap_comp]
  have : (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})).comp (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0, RingHom.comp_id, RingHom.id_comp]
  rw [this]
  exact RelRepS14.specMap_id _

theorem specMap_eqq_eqq_symm {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (C : Type) [CommRing C] [Algebra 𝒪 C]
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] :
    Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom) ≫ Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).symm.toRingHom) =
      𝟙 _ := by
  rw [← RelRepS14.specMap_comp]
  have : (RelRepS14.eqq π C T).toRingHom.comp (RelRepS14.eqq π C T).symm.toRingHom = RingHom.id _ := by
    ext x; simp
  rw [this]
  exact RelRepS14.specMap_id _

noncomputable def xOf9
    (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ Xbar ρ.d //
        x ≫ (qbar ρ.d ≫ ι) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 }) :=
  fun T _ _ _ _ ψT hψT u ρ =>
    ⟨RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ,
     RelRepS14.xPt_over r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB1 hloc T ψT hψT u ρ ι hι₁ hι₂ (tM T u).1 (htM T u) (tM T u).2⟩

theorem ptX_val
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1)
    (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) :
    (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM) d T ψT hψT u ρ hd h0).1 =
      Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫ RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc T ψT hψT u ρ ≫ eqToHom (congrArg Xbar hd) :=
  rfl

theorem W2
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T ψT hψT u ρ hd h0).1) := by
  intro d T T' _ _ _ _ _ _ _ _ φ ψT hψT hψT' u u' ρ ρ' g hg hd hd' h0 h0' hgen hρ
  subst hd
  obtain ⟨hd'', hnat⟩ := xPt_natural r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc (fun d => (hB d).2.2) T T' φ ψT hψT hψT' u u' ρ ρ' g hg hgen hρ
  rw [ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM]
  simp only [eqToHom_refl, Category.comp_id]
  rw [hnat, ← Category.assoc, ← Category.assoc, ← RelRepS14.specMap_comp, ← RelRepS14.specMap_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc T ψT hψT u ρ) (quotEquiv_comp_qmapC π φ h0 h0')

theorem W3
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) ((qbar d ≫ ι) ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T ψT hψT u ρ hd h0 = x) := by
  intro d T _ _ _ _ ψT hψT h0 x

  have hxM : (x.1 ≫ (qbar d ≫ ι) ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) ≫ fM =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T)) := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨u, hu⟩ := hM.ptF_surjective T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T)))
    ⟨x.1 ≫ (qbar d ≫ ι) ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))), hxM⟩
  have hu1 : (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 =
      x.1 ≫ (qbar d ≫ ι) ≫ pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) := congrArg Subtype.val hu

  have hxb₁ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ x.1) ≫ qbar d ≫ pullback.fst fM _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1 := by
    rw [hu1, ← hι₁]; simp only [Category.assoc]
  have hxb₂ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ x.1) ≫ qbar d ≫ pullback.snd fM _ ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C T)) := by
    rw [← hι₂]
    have hx2 := x.2
    simp only [Category.assoc] at hx2 ⊢
    rw [hx2]
  obtain ⟨ρ, hd, hρ⟩ := RelRepX.xPt_surj r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc (fun d => (hB d).2.1) (fun d => (hB d).2.2) d T ψT hψT u
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ x.1) hxb₁ hxb₂
  refine ⟨u, ρ, hd, Subtype.ext ?_⟩
  subst hd
  simp only [eqToHom_refl, Category.comp_id] at hρ
  show Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫
      RelRepS14.xPt r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc T ψT hψT u ρ ≫ eqToHom (congrArg Xbar rfl) = x.1
  simp only [eqToHom_refl, Category.comp_id]
  rw [hρ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0,
    CommRingCat.ofHom_id]
  erw [Spec.map_id]
  exact Category.id_comp _

theorem W4
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)) := by
  intro d T _ _ _ _ ψT hψT h0 u u' ρ ρ' hd hd'
  subst hd
  constructor
  · intro heq
    have h1 := congrArg Subtype.val heq
    rw [ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM] at h1
    simp only [eqToHom_refl, Category.comp_id] at h1

    haveI : IsIso (Spec.map (CommRingCat.ofHom (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom))) :=
      ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))),
        by rw [← RelRepS14.specMap_comp, RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0]; exact RelRepS14.specMap_id _,
        specMap_mk_quotEquiv π h0⟩
    haveI : IsIso (Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).symm.toRingHom)) :=
      ⟨Spec.map (CommRingCat.ofHom (RelRepS14.eqq π C T).toRingHom), specMap_eqq_symm_eqq π C T, specMap_eqq_eqq_symm π C T⟩
    unfold RelRepS14.xPt at h1
    rw [cancel_epi, Category.assoc, cancel_epi] at h1
    have h2 := h1
    exact Alg5X4.iso_of_x0_eq r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc (fun d => (hB d).2.1) (fun d => (hB d).2.2) T ψT hψT h0 u u' ρ ρ' hd' h2.symm
  · rintro ⟨i, hi, hv, ib, hib₁, hib₂, uA, huA, huA', hφ⟩
    have h2 := x0_eq_of_iso r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc (fun d => (hB d).2.2) T ψT hψT u u' ρ ρ' hd' i hi hv ib hib₁ hib₂ uA huA huA' hφ
    apply Subtype.ext
    rw [ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, ptX_val hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM]
    simp only [eqToHom_refl, Category.comp_id]
    unfold RelRepS14.xPt
    rw [Category.assoc, h2]

theorem WM
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM (RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM)) d T ψT hψT u ρ hd h0).1 ≫ (qbar d ≫ ι) ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1) := by
  intro d T _ _ _ _ ψT hψT u ρ hd h0
  subst hd
  simp only [RigidifiedPairClass.ptX, xOf9, eqToHom_refl, Category.comp_id, Category.assoc]
  rw [hι₁, RelRepS14.xPt_fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    RigidifiedPairClass.quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0, Alg5X4.specMap_ofHom_id, Category.id_comp]

theorem WN
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    (∀ (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
          [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
          (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
          (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
          (hd : ρ'.d = ρ.d),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            ((RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM) T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ').1 ≫ eqToHom (congrArg Xbar hd) =
              Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ ((RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM) T ψT hψT u ρ).1) := by
  intro T T' _ _ _ _ _ _ _ _ φ ψT hψT hψT' u u' ρ ρ' g hg hd hP hρ
  obtain ⟨hd', h⟩ := RelRepX.xPt_natural r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc
    (fun d => (hB d).2.2) T T' φ ψT hψT hψT' u u' ρ ρ' g hg hP hρ
  exact h

end RelRepX

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    ∃ xOf : (∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ Xbar ρ.d //
        x ≫ (qbar ρ.d ≫ ι) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 }),

      (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0).1) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) ((qbar d ≫ ι) ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0 = x) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0).1 ≫ (qbar d ≫ ι) ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
          [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
          (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
          (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
          (hd : ρ'.d = ρ.d),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            (xOf T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ').1 ≫ eqToHom (congrArg Xbar hd) =
              Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf T ψT hψT u ρ).1) := by
  exact ⟨RelRepX.xOf9 r π A₀ n fM ptF hM C ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ (fun d => (hB d).1) hloc ι hι₁ hι₂ tM htM,
    RelRepX.W2 hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, RelRepX.W3 hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, RelRepX.W4 hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, RelRepX.WM hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM, RelRepX.WN hrN hrr 𝒪 π hunr Onr hBq Λ hΛ hΛℤ coord hcoord A₀ n hn hrn M fM ptF hM C hC ψ 𝔄 g𝔄 h𝔄 Xbar qbar κ hB hloc ι hι₁ hι₂ tM htM⟩

end S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback (solution)
