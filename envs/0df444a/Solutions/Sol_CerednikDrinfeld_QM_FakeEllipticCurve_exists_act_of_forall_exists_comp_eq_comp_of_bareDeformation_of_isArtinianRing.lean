-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/dc02ca7e-ef0a-5f17-b307-38d4301739ae

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

noncomputable section

namespace ActionFromLiftsAux

universe u

section S0

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem one_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem comp_mul_val {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t f) :
    ψ ≫ (L.mul t P Q).1 =
      (L.mul t' ⟨ψ ≫ P.1, by rw [Category.assoc, P.2, hψ]⟩ ⟨ψ ≫ Q.1, by rw [Category.assoc, Q.2, hψ]⟩).1 :=
  congrArg Subtype.val (L.mul_natural t t' ψ hψ P Q)

theorem comp_one_val {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    ψ ≫ (L.one t).1 = (L.one t').1 :=
  congrArg Subtype.val (L.one_natural t t' ψ hψ)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f)
    (h : L.mul t y y = y) : y = L.one t := by
  calc y = L.mul t (L.mul t y y) (L.inv t y) := by rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
    _ = L.mul t y (L.inv t y) := by rw [h]
    _ = L.one t := L.mul_inv_cancel t y

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  have h1 : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  calc GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)
      = L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) (L.one t') := (L.mul_one t' _).symm
    _ = L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
          (L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
            (L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x))) := by rw [L.mul_inv_cancel]
    _ = L.mul t' (L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
          (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
          (L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by rw [L.mul_assoc]
    _ = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [h1, L.one_mul]

theorem comp_inv_val {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    ψ ≫ (L.inv t x).1 = (L.inv t' ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩).1 :=
  congrArg Subtype.val (inv_natural L t t' ψ hψ x)

theorem one_comp_of_hom {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ φ =
        (L'.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ, P.2]⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 ≫ φ = (L'.one t).1 := by
  set y : SchemeHomOver t f' := ⟨(L.one t).1 ≫ φ, by rw [Category.assoc, hφ, (L.one t).2]⟩ with hy
  have hyy : L'.mul t y y = y := by
    apply Subtype.ext
    have := hom t (L.one t) (L.one t)
    rw [L.one_mul] at this
    exact this.symm
  exact congrArg Subtype.val (eq_one_of_mul_self L' t y hyy)

end S0

section S1

variable {S : Type} [CommRing S] [IsLocalRing S] [IsArtinianRing S]

theorem eq_of_comp_eq_closedFibre {Y A' : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of S)}
    (hY : AbelianSchemePropertyBundle S q) {f' : A' ⟶ Spec (CommRingCat.of S)} (L' : RelativeGroupLaw S f')
    (s : Spec (CommRingCat.of S) ⟶ Y) (hs : s ≫ q = 𝟙 _)
    (u v : Y ⟶ A') (hu : u ≫ f' = q) (hv : v ≫ f' = q)
    (hκ : pullback.fst q (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))) ≫ u =
          pullback.fst q (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))) ≫ v)
    (hsec : s ≫ u = s ≫ v) : u = v := by
  haveI : IsProper q := hY.proper
  haveI : Smooth q := hY.smooth
  have hbij := AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback hY (IsLocalRing.residue S)
    (pullback.snd q (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))
    (pullback.fst q (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))
    (IsPullback.of_hasPullback q _)
  have hinv : Function.Bijective
      ⇑(ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv) :=
    ConcreteCategory.bijective_of_isIso _
  have hf₀ : Function.Bijective
      (pullback.snd q (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)))).appTop :=
    (Function.Bijective.of_comp_iff _ hinv).mp hbij
  exact RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing (IsLocalRing.residue S)
    Ideal.Quotient.mk_surjective L' hf₀ (pullback.fst q _) (IsPullback.of_hasPullback q _) s hs u v hu hv hκ hsec

end S1

section S2

variable {S : Type} [CommRing S] [IsLocalRing S] [IsArtinianRing S] {S₀ : Type} [CommRing S₀] [Algebra S S₀]
  {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} {L₀ : RelativeGroupLaw S₀ f₀}
  (D : BareDeformation f₀ L₀ S)

theorem ker_le_ker_residue (hker : IsNilpotent (RingHom.ker (algebraMap S S₀))) :
    RingHom.ker (algebraMap S S₀) ≤ RingHom.ker (IsLocalRing.residue S) := by
  rw [IsLocalRing.ker_residue]
  apply IsLocalRing.le_maximalIdeal
  intro htop
  obtain ⟨n, hn⟩ := hker
  rw [htop] at hn
  have h1 : (1 : S) ∈ (⊤ : Ideal S) ^ n := by
    have := Ideal.pow_mem_pow (Submodule.mem_top : (1 : S) ∈ (⊤ : Ideal S)) n
    rwa [one_pow] at this
  rw [hn] at h1
  exact one_ne_zero ((Submodule.mem_bot S).mp h1)

def residueFactor (hπ : Function.Surjective (algebraMap S S₀))
    (hker : IsNilpotent (RingHom.ker (algebraMap S S₀))) : S₀ →+* IsLocalRing.ResidueField S :=
  RingHom.liftOfSurjective (algebraMap S S₀) hπ ⟨IsLocalRing.residue S, ker_le_ker_residue hker⟩

theorem residueFactor_comp (hπ : Function.Surjective (algebraMap S S₀))
    (hker : IsNilpotent (RingHom.ker (algebraMap S S₀))) :
    (residueFactor hπ hker).comp (algebraMap S S₀) = IsLocalRing.residue S :=
  RingHom.liftOfSurjective_comp _ _ _

theorem specMap_residue_eq (hπ : Function.Surjective (algebraMap S S₀))
    (hker : IsNilpotent (RingHom.ker (algebraMap S S₀))) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) =
      Spec.map (CommRingCat.ofHom (residueFactor hπ hker)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueFactor_comp]

theorem exists_factor_g (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    {Z : Scheme.{0}} (z : Z ⟶ D.A) (w : Z ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField S)))
    (hz : z ≫ D.f = w ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))) :
    ∃ z₀ : Z ⟶ A₀, z₀ ≫ D.g = z ∧ z₀ ≫ f₀ = w ≫ Spec.map (CommRingCat.ofHom (residueFactor hπ hker)) := by
  refine ⟨D.cart.lift z (w ≫ Spec.map (CommRingCat.ofHom (residueFactor hπ hker))) ?_,
    D.cart.lift_fst _ _ _, D.cart.lift_snd _ _ _⟩
  rw [hz, specMap_residue_eq hπ hker, Category.assoc]

theorem one_comp_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) :
    (L₀.one t).1 ≫ D.g = (D.L.one (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))).1 := by
  set y : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀))) D.f :=
    ⟨(L₀.one t).1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, (L₀.one t).2]⟩ with hy
  have hyy : D.L.mul _ y y = y := by
    apply Subtype.ext
    have := D.hom t (L₀.one t) (L₀.one t)
    rw [L₀.one_mul] at this
    exact this.symm
  exact congrArg Subtype.val (eq_one_of_mul_self D.L _ y hyy)

theorem eq_of_g_comp_eq (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S)} (L' : RelativeGroupLaw S f')
    (u v : D.A ⟶ A') (hu : u ≫ f' = D.f) (hv : v ≫ f' = D.f) (hg : D.g ≫ u = D.g ≫ v)
    (he : (D.L.one (𝟙 _)).1 ≫ u = (D.L.one (𝟙 _)).1 ≫ v) : u = v := by
  apply eq_of_comp_eq_closedFibre D.bundle L' (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).2 u v hu hv _ he
  obtain ⟨z₀, hz₀, -⟩ := exists_factor_g D hπ hker (pullback.fst D.f _) (pullback.snd D.f _) pullback.condition
  rw [← hz₀, Category.assoc, hg, Category.assoc]

theorem eq_of_pair_comp_eq (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S)} (L' : RelativeGroupLaw S f')
    (u v : pullback D.f D.f ⟶ A') (hu : u ≫ f' = prodStr D.f D.f) (hv : v ≫ f' = prodStr D.f D.f)
    (hg : ∀ {Z : Scheme.{0}} (z : Z ⟶ pullback D.f D.f) (w₀ : Z ⟶ Spec (CommRingCat.of S₀)) (z₁ z₂ : Z ⟶ A₀),
      z₁ ≫ f₀ = w₀ → z₂ ≫ f₀ = w₀ →
      z₁ ≫ D.g = z ≫ pullback.fst D.f D.f → z₂ ≫ D.g = z ≫ pullback.snd D.f D.f → z ≫ u = z ≫ v)
    (he : pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ u =
      pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ v) : u = v := by
  have hY : AbelianSchemePropertyBundle S (prodStr D.f D.f) :=
    AbelianSchemePropertyBundle.prodStr_commRing D.bundle D.bundle
  apply eq_of_comp_eq_closedFibre hY L' (pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl)
    (by rw [← Category.assoc, pullback.lift_fst, (D.L.one (𝟙 _)).2]) u v hu hv _ he
  set z := pullback.fst (prodStr D.f D.f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))) with hz
  obtain ⟨z₁, hz₁, hw₁⟩ := exists_factor_g D hπ hker (z ≫ pullback.fst D.f D.f) (pullback.snd (prodStr D.f D.f) _)
    (by rw [Category.assoc]; exact pullback.condition)
  obtain ⟨z₂, hz₂, hw₂⟩ := exists_factor_g D hπ hker (z ≫ pullback.snd D.f D.f) (pullback.snd (prodStr D.f D.f) _)
    (by rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact pullback.condition)
  exact hg z _ z₁ z₂ hw₁ hw₂ hz₁ hz₂

theorem exists_normalised_lift (a₀ : A₀ ⟶ A₀) (ha₀ : (L₀.one (𝟙 _)).1 ≫ a₀ = (L₀.one (𝟙 _)).1)
    (φ : D.A ⟶ D.A) (hφ : φ ≫ D.f = D.f) (hgφ : a₀ ≫ D.g = D.g ≫ φ) :
    ∃ φ' : D.A ⟶ D.A, φ' ≫ D.f = D.f ∧ (D.L.one (𝟙 _)).1 ≫ φ' = (D.L.one (𝟙 _)).1 ∧ a₀ ≫ D.g = D.g ≫ φ' := by

  set e : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) D.f := D.L.one (𝟙 _) with he
  set σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) D.f :=
    ⟨e.1 ≫ φ, by rw [Category.assoc, hφ, e.2]⟩ with hσ
  set τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) D.f := D.L.inv (𝟙 _) σ with hτ

  refine ⟨(D.L.mul D.f ⟨φ, hφ⟩ ⟨D.f ≫ τ.1, by rw [Category.assoc, τ.2, Category.comp_id]⟩).1,
    (D.L.mul D.f _ _).2, ?_, ?_⟩
  ·
    rw [comp_mul_val D.L D.f (𝟙 _) e.1 e.2]
    have h1 : (D.L.mul (𝟙 _) σ τ).1 = e.1 := by rw [hτ, D.L.mul_inv_cancel]
    refine Eq.trans ?_ h1
    apply mul_val_congr D.L rfl
    · rfl
    · show e.1 ≫ D.f ≫ τ.1 = τ.1
      rw [← Category.assoc, e.2, Category.id_comp]
  ·
    set ι := Spec.map (CommRingCat.ofHom (algebraMap S S₀)) with hι
    rw [comp_mul_val D.L D.f (f₀ ≫ ι) D.g D.cart.w]

    have hισ : ι ≫ σ.1 = ι ≫ e.1 := by
      show ι ≫ e.1 ≫ φ = ι ≫ e.1
      have h2 : ι ≫ e.1 = (L₀.one (𝟙 _)).1 ≫ D.g := by
        rw [one_comp_g D (𝟙 _), he]
        rw [comp_one_val D.L (𝟙 _) ι ι (Category.comp_id ι)]
        exact (one_val_congr D.L (Category.id_comp ι)).symm
      rw [← Category.assoc, h2, Category.assoc, ← hgφ, ← Category.assoc, ha₀]

    have hιτ : ι ≫ τ.1 = (D.L.one ι).1 := by
      rw [hτ, comp_inv_val D.L (𝟙 _) ι ι (Category.comp_id ι) σ]
      have h3 : (⟨ι ≫ σ.1, by rw [Category.assoc, σ.2, Category.comp_id]⟩ : SchemeHomOver ι D.f) = D.L.one ι := by
        apply Subtype.ext
        show ι ≫ σ.1 = (D.L.one ι).1
        rw [hισ, comp_one_val D.L (𝟙 _) ι ι (Category.comp_id ι)]
      rw [h3]
      have h4 : D.L.inv ι (D.L.one ι) = D.L.one ι := by
        have := D.L.inv_mul_cancel ι (D.L.one ι)
        rwa [D.L.mul_one] at this
      rw [h4]
    have h5 : (⟨D.g ≫ D.f ≫ τ.1, by rw [Category.assoc, Category.assoc, τ.2, Category.comp_id, D.cart.w]⟩ :
        SchemeHomOver (f₀ ≫ ι) D.f) = D.L.one (f₀ ≫ ι) := by
      apply Subtype.ext
      show D.g ≫ D.f ≫ τ.1 = (D.L.one (f₀ ≫ ι)).1
      rw [← Category.assoc, D.cart.w, Category.assoc, hιτ, comp_one_val D.L ι (f₀ ≫ ι) f₀ rfl]
    rw [hgφ]
    have h6 := congrArg Subtype.val (D.L.mul_one (f₀ ≫ ι) ⟨D.g ≫ φ, by rw [Category.assoc, hφ, D.cart.w]⟩)
    rw [← h5] at h6
    exact h6.symm

end S2

section S3

variable {S : Type} [CommRing S] [IsLocalRing S] [IsArtinianRing S] {S₀ : Type} [CommRing S₀] [Algebra S S₀]
  {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} {L₀ : RelativeGroupLaw S₀ f₀}
  (D : BareDeformation f₀ L₀ S)

theorem comp_mul_global {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f)
    (φ ψ : D.A ⟶ D.A) (hφ : φ ≫ D.f = D.f) (hψ : ψ ≫ D.f = D.f) :
    P.1 ≫ (D.L.mul D.f ⟨φ, hφ⟩ ⟨ψ, hψ⟩).1 =
      (D.L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ, P.2]⟩ ⟨P.1 ≫ ψ, by rw [Category.assoc, hψ, P.2]⟩).1 := by
  rw [comp_mul_val D.L D.f t P.1 P.2]

theorem mul_lift (a₀ b₀ : A₀ ⟶ A₀) (ha₀ : a₀ ≫ f₀ = f₀) (hb₀ : b₀ ≫ f₀ = f₀)
    (φ ψ : D.A ⟶ D.A) (hφ : φ ≫ D.f = D.f) (hψ : ψ ≫ D.f = D.f)
    (heφ : (D.L.one (𝟙 _)).1 ≫ φ = (D.L.one (𝟙 _)).1) (heψ : (D.L.one (𝟙 _)).1 ≫ ψ = (D.L.one (𝟙 _)).1)
    (hgφ : a₀ ≫ D.g = D.g ≫ φ) (hgψ : b₀ ≫ D.g = D.g ≫ ψ) :
    (D.L.one (𝟙 _)).1 ≫ (D.L.mul D.f ⟨φ, hφ⟩ ⟨ψ, hψ⟩).1 = (D.L.one (𝟙 _)).1 ∧
      (L₀.mul f₀ ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩).1 ≫ D.g = D.g ≫ (D.L.mul D.f ⟨φ, hφ⟩ ⟨ψ, hψ⟩).1 := by
  constructor
  · rw [comp_mul_global D (𝟙 _) (D.L.one (𝟙 _)) φ ψ hφ hψ]
    have h1 := congrArg Subtype.val (D.L.one_mul (𝟙 _) (D.L.one (𝟙 _)))
    refine Eq.trans ?_ h1
    exact mul_val_congr D.L rfl _ _ _ _ heφ heψ
  · rw [D.hom f₀ ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩, comp_mul_val D.L D.f _ D.g D.cart.w]
    exact mul_val_congr D.L rfl _ _ _ _ hgφ hgψ

theorem hom_of_lift (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (a₀ : A₀ ⟶ A₀) (ha₀ : a₀ ≫ f₀ = f₀)
    (ha₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ a₀ =
        (L₀.mul t ⟨P.1 ≫ a₀, by rw [Category.assoc, ha₀, P.2]⟩ ⟨Q.1 ≫ a₀, by rw [Category.assoc, ha₀, Q.2]⟩).1)
    (φ : D.A ⟶ D.A) (hφ : φ ≫ D.f = D.f) (heφ : (D.L.one (𝟙 _)).1 ≫ φ = (D.L.one (𝟙 _)).1)
    (hgφ : a₀ ≫ D.g = D.g ≫ φ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f) :
    (D.L.mul t P Q).1 ≫ φ =
      (D.L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ, P.2]⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ, Q.2]⟩).1 := by

  set pr₁ := pullback.fst D.f D.f with hpr₁
  set pr₂ := pullback.snd D.f D.f with hpr₂
  set pt₁ : SchemeHomOver (prodStr D.f D.f) D.f := ⟨pr₁, rfl⟩ with hpt₁
  set pt₂ : SchemeHomOver (prodStr D.f D.f) D.f := ⟨pr₂, pullback_snd_comp_eq_prodStr D.f D.f⟩ with hpt₂
  set u : pullback D.f D.f ⟶ D.A := (D.L.mul (prodStr D.f D.f) pt₁ pt₂).1 ≫ φ with hu
  set v : pullback D.f D.f ⟶ D.A :=
    (D.L.mul (prodStr D.f D.f) ⟨pr₁ ≫ φ, by rw [Category.assoc, hφ]⟩
      ⟨pr₂ ≫ φ, by rw [Category.assoc, hφ, pullback_snd_comp_eq_prodStr]⟩).1 with hv
  have huv : u = v := by
    apply eq_of_pair_comp_eq D hπ hker D.L u v
    · rw [hu, Category.assoc, hφ, (D.L.mul _ pt₁ pt₂).2]
    · exact (D.L.mul _ _ _).2
    · intro Z z w₀ z₁ z₂ hw₁ hw₂ hz₁ hz₂
      have ht : z ≫ prodStr D.f D.f = w₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) := by
        show z ≫ pullback.fst D.f D.f ≫ D.f = _
        rw [← Category.assoc, ← hz₁, Category.assoc, D.cart.w, ← Category.assoc, hw₁]
      rw [hu, hv, ← Category.assoc, comp_mul_val D.L _ _ z rfl, comp_mul_val D.L _ _ z rfl]
      have e1 : (D.L.mul (z ≫ prodStr D.f D.f) ⟨z ≫ pt₁.1, by rw [Category.assoc, pt₁.2]⟩
          ⟨z ≫ pt₂.1, by rw [Category.assoc, pt₂.2]⟩).1 = (L₀.mul w₀ ⟨z₁, hw₁⟩ ⟨z₂, hw₂⟩).1 ≫ D.g := by
        rw [D.hom w₀ ⟨z₁, hw₁⟩ ⟨z₂, hw₂⟩]
        exact mul_val_congr D.L ht _ _ _ _ hz₁.symm hz₂.symm
      rw [e1, Category.assoc, ← hgφ, ← Category.assoc, ha₀hom, D.hom w₀]
      apply mul_val_congr D.L ht.symm
      · show (z₁ ≫ a₀) ≫ D.g = z ≫ pr₁ ≫ φ
        rw [Category.assoc, hgφ, ← Category.assoc, hz₁, Category.assoc]
      · show (z₂ ≫ a₀) ≫ D.g = z ≫ pr₂ ≫ φ
        rw [Category.assoc, hgφ, ← Category.assoc, hz₂, Category.assoc]
    · have hs : pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ prodStr D.f D.f = 𝟙 _ := by
        rw [← Category.assoc, pullback.lift_fst, (D.L.one (𝟙 _)).2]
      rw [hu, hv, ← Category.assoc, comp_mul_val D.L _ _ _ hs, comp_mul_val D.L _ _ _ hs]
      have e2 : (D.L.mul (𝟙 _)
          ⟨pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ pt₁.1, by rw [Category.assoc, pt₁.2, hs]⟩
          ⟨pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ pt₂.1, by rw [Category.assoc, pt₂.2, hs]⟩).1 =
          (D.L.one (𝟙 _)).1 := by
        refine Eq.trans ?_ (congrArg Subtype.val (D.L.one_mul (𝟙 _) (D.L.one (𝟙 _))))
        exact mul_val_congr D.L rfl _ _ _ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      rw [e2, heφ]
      symm
      refine Eq.trans ?_ (congrArg Subtype.val (D.L.one_mul (𝟙 _) (D.L.one (𝟙 _))))
      apply mul_val_congr D.L rfl
      · show pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ pr₁ ≫ φ = _
        rw [← Category.assoc, pullback.lift_fst, heφ]
      · show pullback.lift (D.L.one (𝟙 _)).1 (D.L.one (𝟙 _)).1 rfl ≫ pr₂ ≫ φ = _
        rw [← Category.assoc, pullback.lift_snd, heφ]

  set z : T ⟶ pullback D.f D.f := pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) with hz
  have hzt : z ≫ prodStr D.f D.f = t := by
    show z ≫ pullback.fst D.f D.f ≫ D.f = t
    rw [← Category.assoc, pullback.lift_fst, P.2]
  have key := congrArg (fun k => z ≫ k) huv
  simp only [hu, hv] at key
  rw [← Category.assoc, comp_mul_val D.L _ _ z hzt, comp_mul_val D.L _ _ z hzt] at key
  have lhs : (D.L.mul t P Q).1 =
      (D.L.mul t ⟨z ≫ pt₁.1, by rw [Category.assoc, pt₁.2, hzt]⟩ ⟨z ≫ pt₂.1, by rw [Category.assoc, pt₂.2, hzt]⟩).1 :=
    mul_val_congr D.L rfl _ _ _ _ (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm
  rw [lhs, key]
  apply mul_val_congr D.L rfl
  · show z ≫ pr₁ ≫ φ = P.1 ≫ φ
    rw [← Category.assoc, pullback.lift_fst]
  · show z ≫ pr₂ ≫ φ = Q.1 ≫ φ
    rw [← Category.assoc, pullback.lift_snd]

end S3

end ActionFromLiftsAux

open ActionFromLiftsAux in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (E₀ : FakeEllipticCurve Λ N S₀) (D : BareDeformation E₀.f E₀.L S)
    (hlift : ∀ x : ↥Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ E₀.act x ≫ D.g = D.g ≫ φ) :
    ∃ (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
      ((∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
          pushPt (act x) (act_over x) (D.L.mul t P Q) =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) ∧
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
        (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
          pushPt (act (x + y)) (act_over (x + y)) P =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))) ∧
      (∀ x : ↥Λ, E₀.act x ≫ D.g = D.g ≫ act x) := by

  have act₀_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      (E₀.L.mul t P Q).1 ≫ E₀.act x =
        (E₀.L.mul t ⟨P.1 ≫ E₀.act x, by rw [Category.assoc, E₀.act_over, P.2]⟩
          ⟨Q.1 ≫ E₀.act x, by rw [Category.assoc, E₀.act_over, Q.2]⟩).1 :=
    by intro x T t P Q; exact congrArg Subtype.val (E₀.act_hom x t P Q)
  have act₀_one : ∀ x : ↥Λ, (E₀.L.one (𝟙 _)).1 ≫ E₀.act x = (E₀.L.one (𝟙 _)).1 :=
    fun x => one_comp_of_hom E₀.L E₀.L (E₀.act x) (E₀.act_over x) (act₀_hom x) (𝟙 _)

  have key : ∀ x : ↥Λ, ∃ φ' : D.A ⟶ D.A, φ' ≫ D.f = D.f ∧
      (D.L.one (𝟙 _)).1 ≫ φ' = (D.L.one (𝟙 _)).1 ∧ E₀.act x ≫ D.g = D.g ≫ φ' := fun x => by
    obtain ⟨φ, hφ, hg⟩ := hlift x
    exact exists_normalised_lift D (E₀.act x) (act₀_one x) φ hφ hg
  choose act hact using key
  have hover : ∀ x, act x ≫ D.f = D.f := fun x => (hact x).1
  have hone : ∀ x, (D.L.one (𝟙 _)).1 ≫ act x = (D.L.one (𝟙 _)).1 := fun x => (hact x).2.1
  have hg : ∀ x, E₀.act x ≫ D.g = D.g ≫ act x := fun x => (hact x).2.2

  have hhom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
      (D.L.mul t P Q).1 ≫ act x =
        (D.L.mul t ⟨P.1 ≫ act x, by rw [Category.assoc, hover, P.2]⟩
          ⟨Q.1 ≫ act x, by rw [Category.assoc, hover, Q.2]⟩).1 :=
    by intro x T t P Q; exact hom_of_lift D hπ hker (E₀.act x) (E₀.act_over x) (act₀_hom x) (act x) (hover x) (hone x) (hg x) t P Q
  refine ⟨act, hover, ⟨?_, ?_, ?_, ?_⟩, hg⟩
  ·
    intro x T t P Q
    exact Subtype.ext (hhom x t P Q)
  ·
    intro h
    apply eq_of_g_comp_eq D hπ hker D.L (act ⟨1, h⟩) (𝟙 D.A) (hover _) (Category.id_comp _)
    · rw [← hg, E₀.act_one h, Category.id_comp, Category.comp_id]
    · rw [hone, Category.comp_id]
  ·
    intro x y h
    apply eq_of_g_comp_eq D hπ hker D.L _ _ (hover _) (by rw [Category.assoc, hover, hover])
    · rw [← hg, E₀.act_mul x y h, Category.assoc, hg x, ← Category.assoc, hg y, Category.assoc]
    · rw [hone, ← Category.assoc, hone, hone]
  ·
    intro x y T t P
    have hglob : act (x + y) = (D.L.mul D.f ⟨act x, hover x⟩ ⟨act y, hover y⟩).1 := by
      obtain ⟨h1, h2⟩ := mul_lift D (E₀.act x) (E₀.act y) (E₀.act_over x) (E₀.act_over y) (act x) (act y)
        (hover x) (hover y) (hone x) (hone y) (hg x) (hg y)
      apply eq_of_g_comp_eq D hπ hker D.L _ _ (hover _) (D.L.mul D.f _ _).2
      · rw [← hg, ← h2]
        have h3 := congrArg Subtype.val (E₀.act_add x y E₀.f ⟨𝟙 _, Category.id_comp _⟩)
        change 𝟙 _ ≫ E₀.act (x + y) = _ at h3
        rw [Category.id_comp] at h3
        rw [h3]
        congr 1
      · rw [hone, h1]
    apply Subtype.ext
    show P.1 ≫ act (x + y) = (D.L.mul t ⟨P.1 ≫ act x, _⟩ ⟨P.1 ≫ act y, _⟩).1
    rw [hglob, comp_mul_global D t P]

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing (solution)
