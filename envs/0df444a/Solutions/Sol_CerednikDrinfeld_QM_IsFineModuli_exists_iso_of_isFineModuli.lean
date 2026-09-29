-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_iso_of_isFineModuli
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/70c4ba16-376a-57b6-914b-a75ebdef839d

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_of_isFineModuli
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

open CategoryTheory.Limits

namespace Law3FU

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {B : Type} [CommRing B]

theorem chart
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {M' : Scheme.{0}} {πM' : M' ⟶ Spec (CommRingCat.of B)}
    {ptF' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM'}
    (hM' : IsFineModuli Λ N m M' πM' ptF')
    (R T : CommRingCat.{0}) (α : Spec T ⟶ Spec R) (sR : Spec R ⟶ Spec (CommRingCat.of B))
    (uR : FakeEllipticCurve.WithFullLevel Λ N m ↑R) :
    ∃ uT : FakeEllipticCurve.WithFullLevel Λ N m ↑T,
      (ptF ↑T (α ≫ sR) uT).1 = α ≫ (ptF ↑R sR uR).1 ∧ (ptF' ↑T (α ≫ sR) uT).1 = α ≫ (ptF' ↑R sR uR).1 := by
  obtain ⟨uT, huT⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback (Spec.preimage α).hom uR
  have hα : Spec.map (CommRingCat.ofHom (Spec.preimage α).hom) = α := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨uT, ?_, ?_⟩
  · have := hM.ptF_pullback ↑R ↑T (Spec.preimage α).hom sR (α ≫ sR) (by rw [hα]) uR uT huT
    rw [hα] at this; exact this
  · have := hM'.ptF_pullback ↑R ↑T (Spec.preimage α).hom sR (α ≫ sR) (by rw [hα]) uR uT huT
    rw [hα] at this; exact this

theorem hom_ext_ptF
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) {Y : Scheme.{0}} (g₁ g₂ : M ⟶ Y)
    (h : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S), (ptF S s u).1 ≫ g₁ = (ptF S s u).1 ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext M.affineCover g₁ g₂ fun j => ?_
  let R := M.affineOpenCover.X j
  obtain ⟨u, hu⟩ := hM.ptF_surjective ↑R (M.affineOpenCover.f j ≫ πM) ⟨M.affineOpenCover.f j, rfl⟩
  have h1 : (ptF ↑R (M.affineOpenCover.f j ≫ πM) u).1 = M.affineOpenCover.f j := by rw [hu]
  show M.affineOpenCover.f j ≫ g₁ = M.affineOpenCover.f j ≫ g₂
  rw [← h1]; exact h _ _ u

theorem exists_hom
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {M' : Scheme.{0}} {πM' : M' ⟶ Spec (CommRingCat.of B)}
    {ptF' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM'}
    (hM' : IsFineModuli Λ N m M' πM' ptF') :
    ∃ g : M ⟶ M', g ≫ πM' = πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S), (ptF S s u).1 ≫ g = (ptF' S s u).1 := by
  classical
  let 𝒜 := M.affineOpenCover
  let 𝒰 := M.affineCover
  let sj : ∀ j : 𝒜.I₀, Spec (𝒜.X j) ⟶ Spec (CommRingCat.of B) := fun j => 𝒜.f j ≫ πM
  have hsurj := fun j : 𝒜.I₀ => hM.ptF_surjective ↑(𝒜.X j) (sj j) ⟨𝒜.f j, rfl⟩
  choose u hu using hsurj
  let f : ∀ j : 𝒜.I₀, Spec (𝒜.X j) ⟶ M' := fun j => (ptF' ↑(𝒜.X j) (sj j) (u j)).1
  have hfj : ∀ j, (ptF ↑(𝒜.X j) (sj j) (u j)).1 = 𝒜.f j := fun j => by rw [hu j]

  have key : ∀ (j : 𝒜.I₀) (T : CommRingCat.{0}) (α : Spec T ⟶ Spec (𝒜.X j))
      (v : FakeEllipticCurve.WithFullLevel Λ N m ↑T),
      (ptF ↑T (α ≫ sj j) v).1 = α ≫ 𝒜.f j → (ptF' ↑T (α ≫ sj j) v).1 = α ≫ f j := by
    intro j T α v hv
    obtain ⟨uT, h1', h2⟩ := chart hM hM' (𝒜.X j) T α (sj j) (u j)
    have h1 : (ptF ↑T (α ≫ sj j) uT).1 = α ≫ 𝒜.f j := h1'.trans (congrArg (fun t => α ≫ t) (hfj j))
    have hIso := hM.ptF_injective ↑T (α ≫ sj j) v uT (Subtype.ext (hv.trans h1.symm))
    rw [hM'.ptF_iso ↑T (α ≫ sj j) v uT hIso, h2]; rfl
  have key' : ∀ (j : 𝒜.I₀) (T : CommRingCat.{0}) (α : Spec T ⟶ Spec (𝒜.X j)) (s : Spec T ⟶ Spec (CommRingCat.of B))
      (hs : s = α ≫ sj j) (v : FakeEllipticCurve.WithFullLevel Λ N m ↑T),
      (ptF ↑T s v).1 = α ≫ 𝒜.f j → (ptF' ↑T s v).1 = α ≫ f j := by
    intro j T α s hs v; subst hs; exact key j T α v
  have hcompat : ∀ j k : 𝒜.I₀, pullback.fst (𝒰.f j) (𝒰.f k) ≫ f j = pullback.snd (𝒰.f j) (𝒰.f k) ≫ f k := by
    intro j k
    let V := pullback (𝒰.f j) (𝒰.f k)
    refine Scheme.Cover.hom_ext V.affineCover _ _ fun i => ?_
    let T := V.affineOpenCover.X i
    let w : Spec T ⟶ V := V.affineOpenCover.f i
    show w ≫ pullback.fst (𝒰.f j) (𝒰.f k) ≫ f j = w ≫ pullback.snd (𝒰.f j) (𝒰.f k) ≫ f k
    obtain ⟨v, hv1', -⟩ := chart hM hM' (𝒜.X j) T (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) (sj j) (u j)
    have hv1 : (ptF ↑T ((w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ sj j) v).1 = (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ 𝒜.f j :=
      hv1'.trans (congrArg (fun t => (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ t) (hfj j))
    have hcond : (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ 𝒜.f j = (w ≫ pullback.snd (𝒰.f j) (𝒰.f k)) ≫ 𝒜.f k := by
      show (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ 𝒰.f j = (w ≫ pullback.snd (𝒰.f j) (𝒰.f k)) ≫ 𝒰.f k
      rw [Category.assoc, Category.assoc, pullback.condition]
    have hs : (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ sj j = (w ≫ pullback.snd (𝒰.f j) (𝒰.f k)) ≫ sj k := by
      show (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) ≫ 𝒜.f j ≫ πM = (w ≫ pullback.snd (𝒰.f j) (𝒰.f k)) ≫ 𝒜.f k ≫ πM
      rw [← Category.assoc, hcond, Category.assoc]
    have e1 := key j T (w ≫ pullback.fst (𝒰.f j) (𝒰.f k)) v hv1
    have e2 := key' k T (w ≫ pullback.snd (𝒰.f j) (𝒰.f k)) _ hs v (hv1.trans hcond)
    have h__af := e1.symm.trans e2
    simp only [Category.assoc] at h__af
    exact h__af
  let g : M ⟶ M' := Scheme.Cover.glueMorphisms 𝒰 f hcompat
  have hg : ∀ j, 𝒜.f j ≫ g = f j := fun j => Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat j
  refine ⟨g, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun j => ?_
    show 𝒜.f j ≫ g ≫ πM' = 𝒜.f j ≫ πM
    rw [← Category.assoc, hg]
    exact (ptF' ↑(𝒜.X j) (sj j) (u j)).2
  · intro S _ s uS

    let p : Spec (CommRingCat.of S) ⟶ M := (ptF S s uS).1
    let PC := 𝒰.pullback₁ p
    let 𝒱 : (Spec (CommRingCat.of S)).OpenCover := PC.bind fun j => (PC.X j).affineCover
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun ji => ?_
    obtain ⟨j, i⟩ := ji
    let T := (PC.X j).affineOpenCover.X i
    let w : Spec T ⟶ Spec (CommRingCat.of S) := (PC.X j).affineOpenCover.f i ≫ PC.f j
    let c : Spec T ⟶ Spec (𝒜.X j) := (PC.X j).affineOpenCover.f i ≫ Scheme.Cover.pullbackHom 𝒰 p j
    show w ≫ p ≫ g = w ≫ (ptF' S s uS).1
    have hwc : w ≫ p = c ≫ 𝒜.f j := by
      show ((PC.X j).affineOpenCover.f i ≫ PC.f j) ≫ p = ((PC.X j).affineOpenCover.f i ≫ Scheme.Cover.pullbackHom 𝒰 p j) ≫ 𝒰.f j
      rw [Category.assoc, Category.assoc, Scheme.Cover.pullbackHom_map]

    obtain ⟨uT, h1, h2⟩ := chart hM hM' (CommRingCat.of S) T w s uS
    have hs : w ≫ s = c ≫ sj j := by
      show w ≫ s = c ≫ 𝒜.f j ≫ πM
      rw [← Category.assoc, ← hwc, Category.assoc]
      exact congrArg (fun t => w ≫ t) (ptF S s uS).2.symm
    have e2 := key' j T c (w ≫ s) hs uT (h1.trans hwc)
    rw [← Category.assoc, hwc, Category.assoc, hg, ← e2, h2]

end Law3FU

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {M' : Scheme.{0}} {πM' : M' ⟶ Spec (CommRingCat.of B)}
    {ptF' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM'}
    (hM' : IsFineModuli Λ N m M' πM' ptF') :
    ∃ e : M ≅ M', e.hom ≫ πM' = πM ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF S s u).1 ≫ e.hom = (ptF' S s u).1) ∧
      (∀ g : M ⟶ M', g ≫ πM' = πM →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
          (ptF S s u).1 ≫ g = (ptF' S s u).1) → g = e.hom) := by
  obtain ⟨g, hgπ, hg⟩ := Law3FU.exists_hom hM hM'
  obtain ⟨g', hg'π, hg'⟩ := Law3FU.exists_hom hM' hM
  have h1 : g ≫ g' = 𝟙 M := Law3FU.hom_ext_ptF hM _ _ fun S _ s u => by
    rw [← Category.assoc, hg S s u, hg' S s u, Category.comp_id]
  have h2 : g' ≫ g = 𝟙 M' := Law3FU.hom_ext_ptF hM' _ _ fun S _ s u => by
    rw [← Category.assoc, hg' S s u, hg S s u, Category.comp_id]
  refine ⟨⟨g, g', h1, h2⟩, hgπ, fun S _ s u => hg S s u, ?_⟩
  intro k hkπ hk
  exact Law3FU.hom_ext_ptF hM _ _ fun S _ s u => by rw [hk S s u, hg S s u]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_of_isFineModuli
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_of_isFineModuli (solution)
