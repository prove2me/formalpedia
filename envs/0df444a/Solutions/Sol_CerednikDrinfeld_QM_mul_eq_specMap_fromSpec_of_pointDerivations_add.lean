-- Prove2me | solution 1 for CerednikDrinfeld.QM.mul_eq_specMap_fromSpec_of_pointDerivations_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/63e815f2-3903-553e-9e6c-d0608e719b91

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM AlgebraicGeometry.Scheme.TwoAffineOpenCover"

noncomputable section

namespace S2bAux

section Alg
variable (κ : Type) [Field κ]

abbrev B : Type := TrivSqZeroExt κ (κ × κ)

def ι₁ : DualNumber κ →+* B κ := (TrivSqZeroExt.map (LinearMap.inl κ κ κ)).toRingHom
def ι₂ : DualNumber κ →+* B κ := (TrivSqZeroExt.map (LinearMap.inr κ κ κ)).toRingHom

def σ₁ : B κ →+* DualNumber κ := (TrivSqZeroExt.map (LinearMap.fst κ κ κ)).toRingHom
def σ₂ : B κ →+* DualNumber κ := (TrivSqZeroExt.map (LinearMap.snd κ κ κ)).toRingHom
def Δ : B κ →+* DualNumber κ := (TrivSqZeroExt.map (LinearMap.fst κ κ κ + LinearMap.snd κ κ κ)).toRingHom

@[scoped simp] theorem fst_ι₁ (x : DualNumber κ) : (ι₁ κ x).fst = x.fst := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_ι₁ (x : DualNumber κ) : (ι₁ κ x).snd = (x.snd, 0) := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem fst_ι₂ (x : DualNumber κ) : (ι₂ κ x).fst = x.fst := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_ι₂ (x : DualNumber κ) : (ι₂ κ x).snd = (0, x.snd) := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem fst_σ₁ (x : B κ) : (σ₁ κ x).fst = x.fst := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_σ₁ (x : B κ) : (σ₁ κ x).snd = x.snd.1 := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem fst_σ₂ (x : B κ) : (σ₂ κ x).fst = x.fst := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_σ₂ (x : B κ) : (σ₂ κ x).snd = x.snd.2 := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem fst_Δ (x : B κ) : (Δ κ x).fst = x.fst := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_Δ (x : B κ) : (Δ κ x).snd = x.snd.1 + x.snd.2 := TrivSqZeroExt.snd_map _ _

theorem ext_dual {S : Type} [Semiring S] (f g : S →+* DualNumber κ) (h1 : ∀ s, (f s).fst = (g s).fst)
    (h2 : ∀ s, (f s).snd = (g s).snd) : f = g :=
  RingHom.ext fun s => TrivSqZeroExt.ext (h1 s) (h2 s)

theorem σ₁_comp_ι₁ : (σ₁ κ).comp (ι₁ κ) = RingHom.id _ := by apply ext_dual <;> intro s <;> simp
theorem σ₂_comp_ι₂ : (σ₂ κ).comp (ι₂ κ) = RingHom.id _ := by apply ext_dual <;> intro s <;> simp
theorem Δ_comp_ι₁ : (Δ κ).comp (ι₁ κ) = RingHom.id _ := by apply ext_dual <;> intro s <;> simp
theorem Δ_comp_ι₂ : (Δ κ).comp (ι₂ κ) = RingHom.id _ := by apply ext_dual <;> intro s <;> simp

theorem σ₁_comp_ι₂ : (σ₁ κ).comp (ι₂ κ) = (algebraMap κ (DualNumber κ)).comp (TrivSqZeroExt.fstHom κ κ κ).toRingHom := by
  apply ext_dual <;> intro s <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
theorem σ₂_comp_ι₁ : (σ₂ κ).comp (ι₁ κ) = (algebraMap κ (DualNumber κ)).comp (TrivSqZeroExt.fstHom κ κ κ).toRingHom := by
  apply ext_dual <;> intro s <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ι₁_comp_algebraMap : (ι₁ κ).comp (algebraMap κ (DualNumber κ)) = algebraMap κ (B κ) :=
  (TrivSqZeroExt.map (LinearMap.inl κ κ κ)).comp_algebraMap
theorem ι₂_comp_algebraMap : (ι₂ κ).comp (algebraMap κ (DualNumber κ)) = algebraMap κ (B κ) :=
  (TrivSqZeroExt.map (LinearMap.inr κ κ κ)).comp_algebraMap
theorem σ₁_comp_algebraMap : (σ₁ κ).comp (algebraMap κ (B κ)) = algebraMap κ (DualNumber κ) :=
  (TrivSqZeroExt.map (LinearMap.fst κ κ κ)).comp_algebraMap
theorem σ₂_comp_algebraMap : (σ₂ κ).comp (algebraMap κ (B κ)) = algebraMap κ (DualNumber κ) :=
  (TrivSqZeroExt.map (LinearMap.snd κ κ κ)).comp_algebraMap
theorem Δ_comp_algebraMap : (Δ κ).comp (algebraMap κ (B κ)) = algebraMap κ (DualNumber κ) :=
  (TrivSqZeroExt.map _).comp_algebraMap
theorem fstHom_comp_ι₁ : (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom.comp (ι₁ κ) = (TrivSqZeroExt.fstHom κ κ κ).toRingHom := by
  apply RingHom.ext; intro s; simp
theorem fstHom_comp_ι₂ : (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom.comp (ι₂ κ) = (TrivSqZeroExt.fstHom κ κ κ).toRingHom := by
  apply RingHom.ext; intro s; simp
theorem fstHom_comp_algebraMap_B : (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom.comp (algebraMap κ (B κ)) = RingHom.id κ := by
  apply RingHom.ext; intro s; simp [TrivSqZeroExt.algebraMap_eq_inl]
theorem algebraMap_dual : (algebraMap κ (DualNumber κ)).comp (RingHom.id κ) = algebraMap κ (DualNumber κ) := RingHom.comp_id _

scoped instance : IsLocalRing (B κ) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  by_cases h : x.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
    exact h

theorem comap_fstHom_eq_closedPoint (x : PrimeSpectrum κ) :
    PrimeSpectrum.comap (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom x = IsLocalRing.closedPoint (B κ) := by
  apply PrimeSpectrum.ext
  have hx : x.asIdeal = ⊥ := by
    haveI := PrimeSpectrum.instUnique (R := κ)
    rw [Subsingleton.elim x (⊥ : PrimeSpectrum κ)]; rfl
  ext a
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hx, Ideal.mem_bot]
  show a.fst = 0 ↔ a ∈ IsLocalRing.maximalIdeal (B κ)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]

end Alg

section Plumbing
variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)

theorem hom_eq_of_specMap_fromSpec_eq {S : CommRingCat.{0}} (θ θ' : Γ(X, U) ⟶ S)
    (h : Spec.map θ ≫ hU.fromSpec = Spec.map θ' ≫ hU.fromSpec) : θ = θ' := by
  haveI : Mono hU.fromSpec := inferInstance
  exact Spec.map_injective ((cancel_mono hU.fromSpec).mp h)

theorem exists_eq_specMap_fromSpec (κ : Type) [Field κ] (g : Spec (CommRingCat.of (B κ)) ⟶ X)
    (h : ∀ x : ↥(Spec (CommRingCat.of κ)),
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom) ≫ g).base x ∈ U) :
    ∃ ρ : CommRingCat.of Γ(X, U) ⟶ CommRingCat.of (B κ), g = Spec.map ρ ≫ hU.fromSpec := by
  have hgU : g ⁻¹ᵁ U = ⊤ := by
    have hx := h (IsLocalRing.closedPoint κ)
    change g.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom)).base
      (IsLocalRing.closedPoint κ)) ∈ U at hx
    have : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom)).base (IsLocalRing.closedPoint κ) =
        IsLocalRing.closedPoint (B κ) := comap_fstHom_eq_closedPoint κ _
    rw [this, ← Scheme.Hom.mem_preimage] at hx
    exact (IsLocalRing.closed_point_mem_iff).mp hx
  have hrange : Set.range g.base ⊆ Set.range U.ι.base := by
    rintro y ⟨x, rfl⟩
    have hx : x ∈ g ⁻¹ᵁ U := by rw [hgU]; trivial
    rw [Scheme.Hom.mem_preimage] at hx
    exact ⟨⟨_, hx⟩, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift U.ι g hrange ≫ hU.isoSpec.hom)
  refine ⟨φ, ?_⟩
  rw [hφ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

end Plumbing

end S2bAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add.S2bAux"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add.S2bAux"

open S2bAux in
theorem solution
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1) :
    letI := algebraOfHom fX U
    ∀ (δ δ' : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ χ' χ'' : Γ(X, U) →+* DualNumber κ),
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ' a) = (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ'' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ'' a) = (δ : Γ(X, U) →ₗ[κ] κ) a + (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      ∀ (P P' : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec →
        P'.1 = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec →
        (L.mul (tangentBase κ (RingHom.id κ)) P P').1 = Spec.map (CommRingCat.ofHom χ'') ≫ hU.fromSpec := by
  intro δ δ' χ χ' χ'' hχ1 hχ2 hχ1' hχ2' hχ1'' hχ2'' P P' hP hP'
  classical
  letI alg : Algebra κ Γ(X, U) := algebraOfHom fX U
  set ev : Γ(X, U) →+* κ := ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) with hev_def

  have hι : ⊤ ≤ (e₁ ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; exact le_top
  have heι : e₁ ≫ U.ι = Spec.map ((e₁ ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom) ≫ hU.fromSpec := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec (e₁ ≫ U.ι) hU (isAffineOpen_top _) hι
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have happ : (e₁ ≫ U.ι).appLE U ⊤ hι = U.topIso.inv ≫ e₁.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE e₁ U.ι U ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) le_top]
    congr 1
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hev_hom : CommRingCat.ofHom ev = (e₁ ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom := by
    rw [happ, Category.assoc, hev_def]; rfl
  have heι' : e₁ ≫ U.ι = Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by rw [hev_hom]; exact heι

  have hzero : ∀ χ₀ : Γ(X, U) →+* DualNumber κ, (∀ a, (χ₀ a).fst = ev a) →
      tangentZero κ ≫ Spec.map (CommRingCat.ofHom χ₀) ≫ hU.fromSpec = (L.one (𝟙 _)).1 := by
    intro χ₀ h1
    have hc : (TrivSqZeroExt.fstHom κ κ κ).toRingHom.comp χ₀ = ev := RingHom.ext h1
    rw [← he₁, heι', tangentZero, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]

  let tB2 : Spec (CommRingCat.of (B κ)) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ (B κ)))
  let p₁ : Spec (CommRingCat.of (B κ)) ⟶ Spec (CommRingCat.of (DualNumber κ)) := Spec.map (CommRingCat.ofHom (ι₁ κ))
  let p₂ : Spec (CommRingCat.of (B κ)) ⟶ Spec (CommRingCat.of (DualNumber κ)) := Spec.map (CommRingCat.ofHom (ι₂ κ))
  let s₁ : Spec (CommRingCat.of (DualNumber κ)) ⟶ Spec (CommRingCat.of (B κ)) := Spec.map (CommRingCat.ofHom (σ₁ κ))
  let s₂ : Spec (CommRingCat.of (DualNumber κ)) ⟶ Spec (CommRingCat.of (B κ)) := Spec.map (CommRingCat.ofHom (σ₂ κ))
  let d : Spec (CommRingCat.of (DualNumber κ)) ⟶ Spec (CommRingCat.of (B κ)) := Spec.map (CommRingCat.ofHom (Δ κ))
  let zB : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (B κ)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom)
  have htB : tangentBase κ (RingHom.id κ) = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) := by
    rw [tangentBase, RingHom.comp_id]

  have spec_comp : ∀ {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃),
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
    intro R₁ R₂ R₃ _ _ _ f g
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have spec_id : ∀ {R₁ : Type} [CommRing R₁], Spec.map (CommRingCat.ofHom (RingHom.id R₁)) = 𝟙 _ := by
    intro R₁ _; rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hp₁ : p₁ ≫ tangentBase κ (RingHom.id κ) = tB2 := by rw [htB]; simp only [p₁, tB2, spec_comp, ι₁_comp_algebraMap]
  have hp₂ : p₂ ≫ tangentBase κ (RingHom.id κ) = tB2 := by rw [htB]; simp only [p₂, tB2, spec_comp, ι₂_comp_algebraMap]
  have hs₁ : s₁ ≫ tB2 = tangentBase κ (RingHom.id κ) := by rw [htB]; simp only [s₁, tB2, spec_comp, σ₁_comp_algebraMap]
  have hs₂ : s₂ ≫ tB2 = tangentBase κ (RingHom.id κ) := by rw [htB]; simp only [s₂, tB2, spec_comp, σ₂_comp_algebraMap]
  have hd : d ≫ tB2 = tangentBase κ (RingHom.id κ) := by rw [htB]; simp only [d, tB2, spec_comp, Δ_comp_algebraMap]
  have hz : zB ≫ tB2 = 𝟙 _ := by simp only [zB, tB2, spec_comp, fstHom_comp_algebraMap_B, spec_id]
  have hds₁ : d ≫ p₁ = 𝟙 _ := by simp only [d, p₁, spec_comp, Δ_comp_ι₁, spec_id]
  have hds₂ : d ≫ p₂ = 𝟙 _ := by simp only [d, p₂, spec_comp, Δ_comp_ι₂, spec_id]
  have hs₁p₁ : s₁ ≫ p₁ = 𝟙 _ := by simp only [s₁, p₁, spec_comp, σ₁_comp_ι₁, spec_id]
  have hs₂p₂ : s₂ ≫ p₂ = 𝟙 _ := by simp only [s₂, p₂, spec_comp, σ₂_comp_ι₂, spec_id]
  have hs₁p₂ : s₁ ≫ p₂ = tangentBase κ (RingHom.id κ) ≫ tangentZero κ := by
    rw [htB, tangentZero]; simp only [s₁, p₂, spec_comp, σ₁_comp_ι₂]
  have hs₂p₁ : s₂ ≫ p₁ = tangentBase κ (RingHom.id κ) ≫ tangentZero κ := by
    rw [htB, tangentZero]; simp only [s₂, p₁, spec_comp, σ₂_comp_ι₁]
  have hzp₁ : zB ≫ p₁ = tangentZero κ := by rw [tangentZero]; simp only [zB, p₁, spec_comp, fstHom_comp_ι₁]
  have hzp₂ : zB ≫ p₂ = tangentZero κ := by rw [tangentZero]; simp only [zB, p₂, spec_comp, fstHom_comp_ι₂]

  let P₁ : SchemeHomOver tB2 fX := schemeHomOverComp p₁ hp₁ P
  let P₂ : SchemeHomOver tB2 fX := schemeHomOverComp p₂ hp₂ P'
  let R : SchemeHomOver tB2 fX := L.mul tB2 P₁ P₂

  have hone_tB : (L.one (tangentBase κ (RingHom.id κ))).1 = tangentBase κ (RingHom.id κ) ≫ (L.one (𝟙 _)).1 := by
    have := L.one_natural (𝟙 _) (tangentBase κ (RingHom.id κ)) (tangentBase κ (RingHom.id κ)) (Category.comp_id _)
    rw [← this]; rfl

  have hdiag : L.mul (tangentBase κ (RingHom.id κ)) P P' = schemeHomOverComp d hd R := by
    have e1 : schemeHomOverComp d hd P₁ = P := by
      apply Subtype.ext; show d ≫ (p₁ ≫ P.1) = P.1; rw [← Category.assoc, hds₁, Category.id_comp]
    have e2 : schemeHomOverComp d hd P₂ = P' := by
      apply Subtype.ext; show d ≫ (p₂ ≫ P'.1) = P'.1; rw [← Category.assoc, hds₂, Category.id_comp]
    rw [show schemeHomOverComp d hd R = _ from L.mul_natural tB2 _ d hd P₁ P₂, e1, e2]

  have hRz : zB ≫ R.1 = (L.one (𝟙 _)).1 := by
    have e1 : schemeHomOverComp zB hz P₁ = L.one (𝟙 _) := by
      apply Subtype.ext; show zB ≫ (p₁ ≫ P.1) = (L.one (𝟙 _)).1
      rw [← Category.assoc, hzp₁, hP, hzero χ hχ1]
    have e2 : schemeHomOverComp zB hz P₂ = L.one (𝟙 _) := by
      apply Subtype.ext; show zB ≫ (p₂ ≫ P'.1) = (L.one (𝟙 _)).1
      rw [← Category.assoc, hzp₂, hP', hzero χ' hχ1']
    have := L.mul_natural tB2 _ zB hz P₁ P₂
    rw [e1, e2, L.mul_one] at this
    exact congrArg Subtype.val this
  obtain ⟨ρ', hρ'⟩ := exists_eq_specMap_fromSpec hU κ R.1 (by
    intro x
    rw [show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ (κ × κ)).toRingHom) ≫ R.1 = _ from hRz, ← he₁]
    show U.ι.base (e₁.base x) ∈ U
    exact (e₁.base x).2)
  let ρ : Γ(X, U) →+* B κ := ρ'.hom
  have hρ : R.1 = Spec.map (CommRingCat.ofHom ρ) ≫ hU.fromSpec := hρ'

  have hS₁ : (σ₁ κ).comp ρ = χ := by
    have e1 : schemeHomOverComp s₁ hs₁ P₁ = P := by
      apply Subtype.ext; show s₁ ≫ (p₁ ≫ P.1) = P.1; rw [← Category.assoc, hs₁p₁, Category.id_comp]
    have e2 : schemeHomOverComp s₁ hs₁ P₂ = L.one _ := by
      apply Subtype.ext; show s₁ ≫ (p₂ ≫ P'.1) = (L.one (tangentBase κ (RingHom.id κ))).1
      rw [← Category.assoc, hs₁p₂, hone_tB, Category.assoc, hP', hzero χ' hχ1']
    have := L.mul_natural tB2 _ s₁ hs₁ P₁ P₂
    rw [e1, e2, L.mul_one] at this
    have h := congrArg Subtype.val this
    change s₁ ≫ R.1 = P.1 at h
    rw [hρ, hP, ← Category.assoc] at h
    simp only [s₁, spec_comp] at h
    exact congrArg CommRingCat.Hom.hom (hom_eq_of_specMap_fromSpec_eq hU _ _ h)

  have hS₂ : (σ₂ κ).comp ρ = χ' := by
    have e1 : schemeHomOverComp s₂ hs₂ P₁ = L.one _ := by
      apply Subtype.ext; show s₂ ≫ (p₁ ≫ P.1) = (L.one (tangentBase κ (RingHom.id κ))).1
      rw [← Category.assoc, hs₂p₁, hone_tB, Category.assoc, hP, hzero χ hχ1]
    have e2 : schemeHomOverComp s₂ hs₂ P₂ = P' := by
      apply Subtype.ext; show s₂ ≫ (p₂ ≫ P'.1) = P'.1; rw [← Category.assoc, hs₂p₂, Category.id_comp]
    have := L.mul_natural tB2 _ s₂ hs₂ P₁ P₂
    rw [e1, e2, L.one_mul] at this
    have h := congrArg Subtype.val this
    change s₂ ≫ R.1 = P'.1 at h
    rw [hρ, hP', ← Category.assoc] at h
    simp only [s₂, spec_comp] at h
    exact congrArg CommRingCat.Hom.hom (hom_eq_of_specMap_fromSpec_eq hU _ _ h)

  have hΔρ : (Δ κ).comp ρ = χ'' := by
    apply ext_dual
    · intro a
      rw [hχ1'', ← hχ1 a, ← hS₁]
      simp
    · intro a
      rw [hχ2'', ← hχ2 a, ← hχ2' a, ← hS₁, ← hS₂]
      simp
  rw [hdiag]
  show d ≫ R.1 = _
  rw [hρ, ← Category.assoc]
  simp only [d, spec_comp, hΔρ]

end S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add
end P2MW
export P2MW.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add (solution)
