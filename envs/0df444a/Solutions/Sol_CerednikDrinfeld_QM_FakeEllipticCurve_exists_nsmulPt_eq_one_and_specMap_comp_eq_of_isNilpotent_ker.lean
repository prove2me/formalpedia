-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1424238e-23bc-5fc5-8d77-ccb3889967ca

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit"
namespace QM
p2m_export "CerednikDrinfeld.QM" "nsmulPt FakeEllipticCurve FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit"
namespace LevelEtaleExists
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

universe u

section Yoneda

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (x : SchemeHomOver t f) : nsmulPt L t n x = L.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show L.mul t (nsmulPt L t n x) x = L.mul t (L.nsmul t n x) x
      rw [ih]

theorem coe_nsmul_eq_comp_schemeNsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem coe_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (nsmulPt L t n x).1 = x.1 ≫ L.schemeNsmul n := by
  rw [nsmulPt_eq_nsmul, coe_nsmul_eq_comp_schemeNsmul]

theorem coe_one_comp (L : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    (L.one t').1 = ψ ≫ (L.one t).1 := by
  have := L.one_natural t t' ψ hψ
  rw [← this]
  rfl

end Yoneda

section RingLevel

theorem ΓSpecIso_hom_inv_apply (S : Type u) [CommRing S] (s : S) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) = s := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl

theorem ΓSpecIso_inv_hom_apply (S : Type u) [CommRing S] (x : Γ(Spec (CommRingCat.of S), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl

theorem appTop_specMap_apply {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (x : Γ(Spec (CommRingCat.of S), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom.hom ((Spec.map (CommRingCat.ofHom p)).appTop.hom x) =
      p ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom x) := by
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom p)
  have := congrArg (fun φ => φ.hom x) hnat
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this

theorem isNilpotent_ker_appTop {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hI : IsNilpotent (RingHom.ker p)) :
    IsNilpotent (RingHom.ker (Spec.map (CommRingCat.ofHom p)).appTop.hom) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom).1

  have hker : RingHom.ker (Spec.map (CommRingCat.ofHom p)).appTop.hom =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (RingHom.ker p) := by
    ext x
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx' : p ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom x) = 0 := by
        rw [← appTop_specMap_apply, hx, map_zero]
      rw [← ΓSpecIso_inv_hom_apply S x]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr hx')
    · intro hx
      refine Submodule.span_induction (p := fun y _ => y ∈ RingHom.ker (Spec.map (CommRingCat.ofHom p)).appTop.hom)
        ?_ (zero_mem _) (fun _ _ _ _ h1 h2 => add_mem h1 h2) (fun a _ _ h => Ideal.mul_mem_left _ a h) hx
      rintro _ ⟨s, hs, rfl⟩
      rw [RingHom.mem_ker]
      apply hinj
      rw [map_zero, appTop_specMap_apply, ΓSpecIso_hom_inv_apply]
      exact hs
  change RingHom.ker (Spec.map (CommRingCat.ofHom p)).appTop.hom ^ n = ⊥
  rw [hker, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem surjective_appTop {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) :
    Function.Surjective (Spec.map (CommRingCat.ofHom p)).appTop.hom := by
  intro y
  obtain ⟨s, hs⟩ := hp ((Scheme.ΓSpecIso (CommRingCat.of S₀)).hom.hom y)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s, ?_⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom).1
  apply hinj
  rw [appTop_specMap_apply, ΓSpecIso_hom_inv_apply, hs]

theorem exists_section_lift {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    {X : Scheme.{u}} [IsAffine X] (q : X ⟶ Spec (CommRingCat.of S)) [Smooth q]
    (u₀ : Spec (CommRingCat.of S₀) ⟶ X) (hu₀ : u₀ ≫ q = Spec.map (CommRingCat.ofHom p)) :
    ∃ u : Spec (CommRingCat.of S) ⟶ X, Spec.map (CommRingCat.ofHom p) ≫ u = u₀ ∧ u ≫ q = 𝟙 _ := by
  have hcomp : q.appTop ≫ u₀.appTop = (Spec.map (CommRingCat.ofHom p)).appTop := by
    rw [← Scheme.Hom.comp_appTop, hu₀]

  have hsm : RingHom.Smooth q.appTop.hom := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  letI algX : Algebra Γ(Spec (CommRingCat.of S), ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI alg0 : Algebra Γ(Spec (CommRingCat.of S), ⊤) Γ(Spec (CommRingCat.of S₀), ⊤) :=
    (Spec.map (CommRingCat.ofHom p)).appTop.hom.toAlgebra
  haveI : Algebra.FormallySmooth Γ(Spec (CommRingCat.of S), ⊤) Γ(X, ⊤) := hsm.formallySmooth.toAlgebra

  let f : Γ(X, ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S₀), ⊤) :=
    { u₀.appTop.hom with
      commutes' := fun r => by
        change u₀.appTop.hom (q.appTop.hom r) = (Spec.map (CommRingCat.ofHom p)).appTop.hom r
        rw [← CommRingCat.comp_apply, hcomp] }
  let g : Γ(Spec (CommRingCat.of S), ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S₀), ⊤) :=
    Algebra.ofId _ _
  have hg : Function.Surjective g := surjective_appTop p hp
  have hg' : IsNilpotent (RingHom.ker (g : Γ(Spec (CommRingCat.of S), ⊤) →+* Γ(Spec (CommRingCat.of S₀), ⊤))) :=
    isNilpotent_ker_appTop p hI

  let ψ : Γ(X, ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S), ⊤) :=
    Algebra.FormallySmooth.liftOfSurjective f g hg hg'
  have hψf : ∀ x, (Spec.map (CommRingCat.ofHom p)).appTop.hom (ψ x) = u₀.appTop.hom x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply f g hg hg' x
  have hψφ : ∀ r, ψ (q.appTop.hom r) = r := fun r => ψ.commutes r

  let ψ' : Γ(X, ⊤) ⟶ Γ(Spec (CommRingCat.of S), ⊤) := CommRingCat.ofHom ψ.toRingHom
  have h1 : q.appTop ≫ ψ' = 𝟙 _ := by
    ext r
    exact hψφ r
  have h2 : ψ' ≫ (Spec.map (CommRingCat.ofHom p)).appTop = u₀.appTop := by
    ext x
    exact hψf x

  refine ⟨(Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map ψ' ≫ X.isoSpec.inv, ?_, ?_⟩
  ·
    have hn := Scheme.isoSpec_hom_naturality (Spec.map (CommRingCat.ofHom p))
    have hu := Scheme.isoSpec_inv_naturality u₀
    calc Spec.map (CommRingCat.ofHom p) ≫ (Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map ψ' ≫ X.isoSpec.inv
        = ((Spec (CommRingCat.of S₀)).isoSpec.hom ≫ Spec.map (Spec.map (CommRingCat.ofHom p)).appTop) ≫
            Spec.map ψ' ≫ X.isoSpec.inv := by
          rw [hn, Category.assoc]
      _ = (Spec (CommRingCat.of S₀)).isoSpec.hom ≫
            (Spec.map (Spec.map (CommRingCat.ofHom p)).appTop ≫ Spec.map ψ') ≫ X.isoSpec.inv := by
          simp only [Category.assoc]
      _ = (Spec (CommRingCat.of S₀)).isoSpec.hom ≫
            Spec.map (ψ' ≫ (Spec.map (CommRingCat.ofHom p)).appTop) ≫ X.isoSpec.inv := by
          rw [Spec.map_comp]
      _ = (Spec (CommRingCat.of S₀)).isoSpec.hom ≫ Spec.map u₀.appTop ≫ X.isoSpec.inv := by rw [h2]
      _ = (Spec (CommRingCat.of S₀)).isoSpec.hom ≫ (Spec (CommRingCat.of S₀)).isoSpec.inv ≫ u₀ := by rw [hu]
      _ = u₀ := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  ·
    have hq := Scheme.isoSpec_inv_naturality q
    calc ((Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map ψ' ≫ X.isoSpec.inv) ≫ q
        = (Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map ψ' ≫ (X.isoSpec.inv ≫ q) := by
          simp only [Category.assoc]
      _ = (Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map ψ' ≫
            (Spec.map q.appTop ≫ (Spec (CommRingCat.of S)).isoSpec.inv) := by rw [hq]
      _ = (Spec (CommRingCat.of S)).isoSpec.hom ≫ (Spec.map ψ' ≫ Spec.map q.appTop) ≫
            (Spec (CommRingCat.of S)).isoSpec.inv := by simp only [Category.assoc]
      _ = (Spec (CommRingCat.of S)).isoSpec.hom ≫ Spec.map (q.appTop ≫ ψ') ≫
            (Spec (CommRingCat.of S)).isoSpec.inv := by rw [Spec.map_comp]
      _ = 𝟙 _ := by rw [h1, Spec.map_id, Category.id_comp, Iso.hom_inv_id]

end RingLevel

end CerednikDrinfeld.QM.LevelEtaleExists

open CerednikDrinfeld.QM.LevelEtaleExists in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (P₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom p)) E.f)
    (hP₀ : nsmulPt E.L (Spec.map (CommRingCat.ofHom p)) m P₀ = E.L.one (Spec.map (CommRingCat.ofHom p))) :
    ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S))) ∧
      Spec.map (CommRingCat.ofHom p) ≫ P.1 = P₀.1 := by

  have h0 : P₀.1 ≫ E.L.schemeNsmul m =
      Spec.map (CommRingCat.ofHom p) ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [← coe_nsmulPt, hP₀]
    exact coe_one_comp E.L (𝟙 _) (Spec.map (CommRingCat.ofHom p)) (Spec.map (CommRingCat.ofHom p))
      (Category.comp_id _)
  have hu₀fst : pullback.lift P₀.1 (Spec.map (CommRingCat.ofHom p)) h0 ≫ pullback.fst _ _ = P₀.1 :=
    pullback.lift_fst _ _ _
  have hu₀snd : pullback.lift P₀.1 (Spec.map (CommRingCat.ofHom p)) h0 ≫ E.L.schemeKerStr m =
      Spec.map (CommRingCat.ofHom p) :=
    pullback.lift_snd _ _ _

  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E m hm
  haveI := hfin
  haveI := het
  haveI : IsAffine (E.L.schemeKer m) := isAffine_of_isAffineHom (E.L.schemeKerStr m)
  haveI : Smooth (E.L.schemeKerStr m) := inferInstance

  obtain ⟨u, hu, huq⟩ := exists_section_lift p hp hI (E.L.schemeKerStr m)
    (pullback.lift P₀.1 (Spec.map (CommRingCat.ofHom p)) h0) hu₀snd

  have hcond : pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.L.schemeNsmul m =
      pullback.snd _ _ ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
    pullback.condition
  have hPm : (u ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫
      E.L.schemeNsmul m = (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [Category.assoc, hcond, ← Category.assoc]
    change (u ≫ E.L.schemeKerStr m) ≫ _ = _
    rw [huq, Category.id_comp]
  have hPf : (u ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ E.f = 𝟙 _ := by
    have h' : (u ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ E.f =
        ((u ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫
          E.L.schemeNsmul m) ≫ E.f := by
      rw [Category.assoc _ (E.L.schemeNsmul m) E.f, E.L.schemeNsmul_over]
    rw [h', hPm]
    exact (E.L.one (𝟙 _)).2
  refine ⟨⟨u ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1, hPf⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_nsmulPt]
    exact hPm
  · change Spec.map (CommRingCat.ofHom p) ≫ u ≫ pullback.fst _ _ = P₀.1
    rw [← Category.assoc, hu, hu₀fst]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker (solution)
