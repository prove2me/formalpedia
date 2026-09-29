-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.existsUnique_hom_ptF_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d52f0387-9996-5709-87e2-2d31bcfdc668

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptF_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace ChartGlue

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

theorem iso_fst_of_iso {S : Type} [CommRing S] {u u' : FakeEllipticCurve.WithFullLevel Λ N m S}
    (h : FakeEllipticCurve.WithFullLevel.Iso u u') : FakeEllipticCurve.Iso u.1 u'.1 := by
  obtain ⟨e, he, hmul, hact, hlev, -⟩ := h
  exact ⟨e, he, hmul, hact, hlev⟩

theorem isPullback_fst_of_isPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {u : FakeEllipticCurve.WithFullLevel Λ N m S} {u' : FakeEllipticCurve.WithFullLevel Λ N m S'}
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') : FakeEllipticCurve.IsPullback φ u.1 u'.1 := by
  obtain ⟨g, hg, hmul, hact, hlev, -⟩ := h
  exact ⟨g, hg, hmul, hact, hlev⟩

private theorem _root_.ChartGlue.exists_isPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.WithFullLevel.IsPullback φ u u' :=
  CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback φ u

p2m_export "ChartGlue" "exists_isPullback"

section Charts

variable {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF)
  {T : Scheme.{0}} (πT : T ⟶ Spec (CommRingCat.of 𝒪))
  (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve Λ N S → SchemeHomOver s πT)
  (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
    FakeEllipticCurve.Iso E E' → pt' S s E = pt' S s E')
  (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' → (pt' S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).1)

include hM hiso hpb in

theorem comp_pt'_eq_of_comp_ptF_eq {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C]
    (sR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪)) (sR' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (v : FakeEllipticCurve.WithFullLevel Λ N m R')
    (α : R →+* C) (β : R' →+* C)
    (hs : Spec.map (CommRingCat.ofHom α) ≫ sR = Spec.map (CommRingCat.ofHom β) ≫ sR')
    (h : Spec.map (CommRingCat.ofHom α) ≫ (ptF R sR u).1 = Spec.map (CommRingCat.ofHom β) ≫ (ptF R' sR' v).1) :
    Spec.map (CommRingCat.ofHom α) ≫ (pt' R sR u.1).1 = Spec.map (CommRingCat.ofHom β) ≫ (pt' R' sR' v.1).1 := by
  obtain ⟨u', hu'⟩ := exists_isPullback α u
  obtain ⟨v', hv'⟩ := exists_isPullback β v
  let sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪) := Spec.map (CommRingCat.ofHom α) ≫ sR
  have h1 := hM.ptF_pullback R C α sR sC rfl u u' hu'
  have h2 := hM.ptF_pullback R' C β sR' sC hs.symm v v' hv'
  have h12 : ptF C sC u' = ptF C sC v' := Subtype.ext (by rw [h1, h2, h])
  have hI : FakeEllipticCurve.Iso u'.1 v'.1 := iso_fst_of_iso (hM.ptF_injective C sC u' v' h12)
  have h3 := hpb R C α sR sC rfl u.1 u'.1 (isPullback_fst_of_isPullback α hu')
  have h4 := hpb R' C β sR' sC hs.symm v.1 v'.1 (isPullback_fst_of_isPullback β hv')
  rw [← h3, ← h4, hiso C sC _ _ hI]

end Charts

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt' S s E = pt' S s E')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt' S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).1) :
    ∃! Φ : M ⟶ T, Φ ≫ πT = πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S), (pt' S s u.1).1 = (ptF S s u).1 ≫ Φ := by
  classical

  let A : M.affineCover.I₀ → CommRingCat.{0} := fun j => M.affineOpenCover.X j
  let ι : ∀ j, Spec (CommRingCat.of (A j)) ⟶ M := fun j => M.affineCover.f j
  let s : ∀ j, Spec (CommRingCat.of (A j)) ⟶ Spec (CommRingCat.of 𝒪) := fun j => ι j ≫ πM
  have hu : ∀ j, ∃ u : FakeEllipticCurve.WithFullLevel Λ N m (A j), ptF (A j) (s j) u = ⟨ι j, rfl⟩ :=
    fun j => hM.ptF_surjective (A j) (s j) ⟨ι j, rfl⟩
  choose u hu using hu
  let φ : ∀ j, Spec (CommRingCat.of (A j)) ⟶ T := fun j => (pt' (A j) (s j) (u j).1).1

  have key : ∀ {C : Type} [CommRing C] (j : M.affineCover.I₀) {S : Type} [CommRing S]
      (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (v : FakeEllipticCurve.WithFullLevel Λ N m S)
      (γ : S →+* C) (δ : (A j) →+* C),
      Spec.map (CommRingCat.ofHom γ) ≫ (ptF S sS v).1 = Spec.map (CommRingCat.ofHom δ) ≫ ι j →
      Spec.map (CommRingCat.ofHom γ) ≫ (pt' S sS v.1).1 = Spec.map (CommRingCat.ofHom δ) ≫ φ j := by
    intro C _ j S _ sS v γ δ h
    refine comp_pt'_eq_of_comp_ptF_eq hM πT pt' hiso hpb sS (s j) v (u j) γ δ ?_ ?_
    · rw [← (ptF S sS v).2, ← Category.assoc, h, Category.assoc]
    · rw [h, hu j]

  have hφ : ∀ i j, Limits.pullback.fst (ι i) (ι j) ≫ φ i = Limits.pullback.snd (ι i) (ι j) ≫ φ j := by
    intro i j
    refine Scheme.Cover.hom_ext (Limits.pullback (ι i) (ι j)).affineCover _ _ fun k => ?_
    let w := (Limits.pullback (ι i) (ι j)).affineCover.f k
    have hα : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst (ι i) (ι j))) = w ≫ Limits.pullback.fst (ι i) (ι j) :=
      Spec.map_preimage _
    have hβ : Spec.map (Spec.preimage (w ≫ Limits.pullback.snd (ι i) (ι j))) = w ≫ Limits.pullback.snd (ι i) (ι j) :=
      Spec.map_preimage _
    rw [← Category.assoc, ← Category.assoc, ← hα, ← hβ]
    have hk := key i (s j) (u j) (Spec.preimage (w ≫ Limits.pullback.snd (ι i) (ι j))).hom
      (Spec.preimage (w ≫ Limits.pullback.fst (ι i) (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    refine (hk ?_).symm
    rw [hu j, hα, hβ]
    show (w ≫ _) ≫ ι j = (w ≫ _) ≫ ι i
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  let Φ : M ⟶ T := Scheme.Cover.glueMorphisms M.affineCover φ hφ
  have hΦι : ∀ j, ι j ≫ Φ = φ j := fun j => Scheme.Cover.ι_glueMorphisms M.affineCover φ hφ j

  have hprop : ∀ (S : Type) [CommRing S] (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (v : FakeEllipticCurve.WithFullLevel Λ N m S), (pt' S sS v.1).1 = (ptF S sS v).1 ≫ Φ := by
    intro S _ sS v
    let y := (ptF S sS v).1
    refine Scheme.Cover.hom_ext (M.affineCover.pullback₁ y) _ _ fun j => ?_
    change Limits.pullback.fst y (ι j) ≫ (pt' S sS v.1).1 = Limits.pullback.fst y (ι j) ≫ (y ≫ Φ)
    refine Scheme.Cover.hom_ext (Limits.pullback y (ι j)).affineCover _ _ fun k => ?_
    let w := (Limits.pullback y (ι j)).affineCover.f k
    show w ≫ Limits.pullback.fst y (ι j) ≫ (pt' S sS v.1).1 = w ≫ Limits.pullback.fst y (ι j) ≫ (y ≫ Φ)
    have hγ : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) = w ≫ Limits.pullback.fst y (ι j) := Spec.map_preimage _
    have hδ : Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) = w ≫ Limits.pullback.snd y (ι j) := Spec.map_preimage _
    rw [← Category.assoc, ← Category.assoc, ← hγ]
    have hk := key j sS v (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))).hom (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    have hc : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) ≫ (ptF S sS v).1 =
        Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) ≫ ι j := by
      rw [hγ, hδ]
      show (w ≫ _) ≫ y = (w ≫ _) ≫ ι j
      rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    have hk' := hk hc
    refine hk'.trans ?_
    show Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) ≫ φ j =
      Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) ≫ y ≫ Φ
    rw [← hΦι j, ← Category.assoc, ← Category.assoc]
    congr 1
    exact hc.symm
  refine ⟨Φ, ⟨?_, hprop⟩, ?_⟩
  ·
    refine Scheme.Cover.hom_ext M.affineCover _ _ fun j => ?_
    change (ι j ≫ Φ) ≫ πT = ι j ≫ πM
    rw [hΦι j]
    exact (pt' (A j) (s j) (u j).1).2
  ·
    rintro Φ' ⟨-, hΦ'⟩
    refine Scheme.Cover.hom_ext M.affineCover _ _ fun j => ?_
    change ι j ≫ Φ' = ι j ≫ Φ
    rw [hΦι j]
    have := hΦ' (A j) (s j) (u j)
    rw [hu j] at this
    exact this.symm

end ChartGlue

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt' S s E = pt' S s E')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt' S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).1) :
    ∃! Φ : M ⟶ T, Φ ≫ πT = πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S), (pt' S s u.1).1 = (ptF S s u).1 ≫ Φ :=
  ChartGlue.solution hM T πT pt' hiso hpb

end S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptF_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptF_comp_eq (solution)
