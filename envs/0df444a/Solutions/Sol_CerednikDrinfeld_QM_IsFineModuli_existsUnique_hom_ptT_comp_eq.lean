-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.existsUnique_hom_ptT_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c137f5ab-b13c-5b0a-b1b7-e84f70f32eac

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_extraLevel_forall_factorsThrough_iff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptT_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace ChartGlueT

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

def Gen (ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type} [CommRing S]
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
    FactorsThrough K.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (w.1.act x) (w.1.act_over x)
          (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q

def Disj (ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type} [CommRing S]
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
    FactorsThrough w.1.lev
      (pushPt (w.1.act x) (w.1.act_over x)
        (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk))) →
    pushPt (w.1.act x) (w.1.act_over x)
        (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = w.1.L.one (geomPoint k sk)

section IsoGen

variable {S : Type} [CommRing S] {E E' : FakeEllipticCurve Λ N S} (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)

include he in
theorem he_inv : e.inv ≫ E.f = E'.f := by rw [← he, e.inv_hom_id_assoc]

theorem mapPt_injective {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {P Q : SchemeHomOver t E.f}
    (h : mapPt e.hom he P = mapPt e.hom he Q) : P = Q := by
  apply Subtype.ext
  have h1 := congrArg Subtype.val h
  rw [mapPt_coe, mapPt_coe] at h1
  exact (cancel_mono e.hom).mp h1

theorem mapPt_mapPt_inv {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E'.f) :
    mapPt e.hom he (mapPt e.inv (he_inv e he) Q) = Q := by
  apply Subtype.ext
  rw [mapPt_coe, mapPt_coe, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem mapPt_pushPt (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) (x : ↥Λ)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    mapPt e.hom he (pushPt (E.act x) (E.act_over x) P) = pushPt (E'.act x) (E'.act_over x) (mapPt e.hom he P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc, hact]

include he in
theorem mapPt_one
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt e.hom he (E.L.one t) = E'.L.one t := by
  letI := E.L.pointGroup t
  letI := E'.L.pointGroup t
  have h1 : mapPt e.hom he (E.L.one t) = E'.L.mul t (mapPt e.hom he (E.L.one t)) (mapPt e.hom he (E.L.one t)) := by
    rw [← hmul]; congr 1; exact (E.L.one_mul t _).symm

  have : (mapPt e.hom he (E.L.one t) : SchemeHomOver t E'.f) = 1 := by
    have h2 : (mapPt e.hom he (E.L.one t)) * (mapPt e.hom he (E.L.one t)) = (mapPt e.hom he (E.L.one t)) * 1 := by
      rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  exact this

include he in
theorem mapPt_nsmulPt
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    mapPt e.hom he (nsmulPt E.L t n P) = nsmulPt E'.L t n (mapPt e.hom he P) := by
  induction n with
  | zero => exact mapPt_one e he hmul t
  | succ n ih =>
    show mapPt e.hom he (E.L.mul t (nsmulPt E.L t n P) P) = E'.L.mul t (nsmulPt E'.L t n (mapPt e.hom he P)) (mapPt e.hom he P)
    rw [hmul, ih]

theorem mapPt_sectionAt (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type) [Field k] (sk : S →+* k) :
    mapPt e.hom he (FakeEllipticCurve.sectionAt P k sk) = FakeEllipticCurve.sectionAt (mapPt e.hom he P) k sk := by
  apply Subtype.ext
  simp only [mapPt_coe]
  exact Category.assoc _ _ _

end IsoGen

theorem iso_pair_of_iso (ℓ : ℕ) (hℓ : ℓ.Prime) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type} [CommRing S] (hℓS : IsUnit ((ℓ : ℕ) : S))
    {u v : FakeEllipticCurve.WithFullLevel Λ N m S} (h : FakeEllipticCurve.WithFullLevel.Iso u v)
    (Ku : u.1.ExtraLevel ℓ) (Kv : v.1.ExtraLevel ℓ) (hu : Gen ℓ L₀ u Ku) (hv : Gen ℓ L₀ v Kv) :
    FakeEllipticCurve.WithExtraLevel.Iso (⟨u.1, Ku⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨v.1, Kv⟩ := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h

  obtain ⟨K'', hK''⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff ℓ u.1 v.1 e he hmul hact hlev Ku

  have hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) v.1.f),
      FactorsThrough K''.levK Q ↔ FactorsThrough Kv.levK Q := by
    intro k _ _ sk Q
    have htrans : ∀ x : ↥Λ,
        mapPt e.hom he (pushPt (u.1.act x) (u.1.act_over x)
          (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk))) =
        pushPt (v.1.act x) (v.1.act_over x)
          (nsmulPt v.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt v.2.P k sk)) := by
      intro x
      rw [mapPt_pushPt e he hact, mapPt_nsmulPt e he hmul, mapPt_sectionAt e he, hP]
    rw [← mapPt_mapPt_inv e he Q, hK'', hu k sk, hv k sk]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    constructor
    · intro h; rw [← h, htrans]
    · intro h; exact mapPt_injective e he (by rw [htrans, h])
  refine ⟨e, he, hmul, hact, hlev, ?_⟩
  intro T t P
  show FactorsThrough Ku.levK P ↔ FactorsThrough Kv.levK (mapPt e.hom he P)
  rw [← hK'' t P]
  exact CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_iff_of_forall_geomPoint ℓ hℓ hℓS v.1 K'' Kv hgeom t
    (mapPt e.hom he P)

section Charts

variable {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF)
  (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
  {T : Scheme.{0}} (πT : T ⟶ Spec (CommRingCat.of 𝒪))
  (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT)
  (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u')
  (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1)

include hM hℓ hℓm hiso hpb in
theorem comp_pt'_eq_of_comp_ptF_eq {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C]
    (hmR : IsUnit ((m : ℕ) : R)) (hmR' : IsUnit ((m : ℕ) : R')) (hℓC : IsUnit ((ℓ : ℕ) : C))
    (sR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪)) (sR' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (Ku : u.1.ExtraLevel ℓ) (hKu : Gen ℓ L₀ u Ku)
    (v : FakeEllipticCurve.WithFullLevel Λ N m R') (Kv : v.1.ExtraLevel ℓ) (hKv : Gen ℓ L₀ v Kv)
    (α : R →+* C) (β : R' →+* C)
    (hs : Spec.map (CommRingCat.ofHom α) ≫ sR = Spec.map (CommRingCat.ofHom β) ≫ sR')
    (h : Spec.map (CommRingCat.ofHom α) ≫ (ptF R sR u).1 = Spec.map (CommRingCat.ofHom β) ≫ (ptF R' sR' v).1) :
    Spec.map (CommRingCat.ofHom α) ≫ (pt' R sR ⟨u.1, Ku⟩).1 = Spec.map (CommRingCat.ofHom β) ≫ (pt' R' sR' ⟨v.1, Kv⟩).1 := by
  obtain ⟨u', Ku', hu', hu'T, hGu⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff m ℓ hℓ hℓm L₀ α hmR u Ku
  obtain ⟨v', Kv', hv', hv'T, hGv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff m ℓ hℓ hℓm L₀ β hmR' v Kv
  let sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪) := Spec.map (CommRingCat.ofHom α) ≫ sR
  have h1 := hM.ptF_pullback R C α sR sC rfl u u' hu'
  have h2 := hM.ptF_pullback R' C β sR' sC hs.symm v v' hv'
  have h12 : ptF C sC u' = ptF C sC v' := Subtype.ext (by rw [h1, h2, h])
  have hI : FakeEllipticCurve.WithExtraLevel.Iso (⟨u'.1, Ku'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ C) ⟨v'.1, Kv'⟩ :=
    iso_pair_of_iso ℓ hℓ L₀ hℓC (hM.ptF_injective C sC u' v' h12) Ku' Kv' (hGu hKu) (hGv hKv)
  have h3 := hpb R C α sR sC rfl ⟨u.1, Ku⟩ ⟨u'.1, Ku'⟩ hu'T
  have h4 := hpb R' C β sR' sC hs.symm ⟨v.1, Kv⟩ ⟨v'.1, Kv'⟩ hv'T
  rw [← h3, ← h4, hiso C sC _ _ hI]

end Charts

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N m : ℕ} {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (V : M.Opens)
    (hV : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (w : FakeEllipticCurve.WithFullLevel Λ N m S),
      Set.range (ptF S s w).1 ⊆ (V : Set ↥M) ↔
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough w.1.lev
          (pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk))) →
        pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = w.1.L.one (geomPoint k sk))
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1) :
    ∃! Φ : (V : Scheme.{0}) ⟶ T, Φ ≫ πT = V.ι ≫ πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) (x : Spec (CommRingCat.of S) ⟶ (V : Scheme.{0})),
        x ≫ V.ι = (ptF S s w).1 →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        (pt' S s ⟨w.1, K⟩).1 = x ≫ Φ := by
  classical

  have hunit : ∀ {S : Type} [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), IsUnit ((m : ℕ) : S) := by
    intro S _ s
    have := hm'.map (Spec.preimage s).hom
    rwa [map_natCast] at this
  have hℓunit : ∀ {S : Type} [CommRing S], IsUnit ((m : ℕ) : S) → IsUnit ((ℓ : ℕ) : S) := by
    intro S _ h
    obtain ⟨c, hc⟩ := hℓm
    rw [hc, Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h

  let VS : Scheme.{0} := (V : Scheme.{0})
  let A : VS.affineCover.I₀ → CommRingCat.{0} := fun j => VS.affineOpenCover.X j
  let ι : ∀ j, Spec (CommRingCat.of (A j)) ⟶ VS := fun j => VS.affineCover.f j
  let y : ∀ j, Spec (CommRingCat.of (A j)) ⟶ M := fun j => ι j ≫ V.ι
  let s : ∀ j, Spec (CommRingCat.of (A j)) ⟶ Spec (CommRingCat.of 𝒪) := fun j => y j ≫ πM
  have hu : ∀ j, ∃ u : FakeEllipticCurve.WithFullLevel Λ N m (A j), ptF (A j) (s j) u = ⟨y j, rfl⟩ :=
    fun j => hM.ptF_surjective (A j) (s j) ⟨y j, rfl⟩
  choose u hu using hu
  have hdisj : ∀ j, Disj ℓ L₀ (u j) := by
    intro j
    refine (hV (A j) (s j) (u j)).mp ?_
    rw [hu j]
    rintro _ ⟨z, rfl⟩
    show (ι j ≫ V.ι).base z ∈ (V : Set ↥M)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ← Scheme.Opens.range_ι V]
    exact ⟨_, rfl⟩
  have hK : ∀ j, ∃ K : (u j).1.ExtraLevel ℓ, Gen ℓ L₀ (u j) K := fun j =>
    CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_extraLevel_forall_factorsThrough_iff hB Λ hΛ m ℓ hℓ hℓm L₀ hL₀ hℓL₀
      hL₀_left hL₀_index (hunit (s j)) (u j).1 (u j).2 (hdisj j)
  choose K hK using hK
  let φ : ∀ j, Spec (CommRingCat.of (A j)) ⟶ T := fun j => (pt' (A j) (s j) ⟨(u j).1, K j⟩).1

  have key : ∀ {C : Type} [CommRing C] (j : VS.affineCover.I₀) {S : Type} [CommRing S]
      (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (w : FakeEllipticCurve.WithFullLevel Λ N m S)
      (Kw : w.1.ExtraLevel ℓ) (hKw : Gen ℓ L₀ w Kw) (γ : S →+* C) (δ : (A j) →+* C),
      Spec.map (CommRingCat.ofHom γ) ≫ (ptF S sS w).1 = Spec.map (CommRingCat.ofHom δ) ≫ y j →
      Spec.map (CommRingCat.ofHom γ) ≫ (pt' S sS ⟨w.1, Kw⟩).1 = Spec.map (CommRingCat.ofHom δ) ≫ φ j := by
    intro C _ j S _ sS w Kw hKw γ δ h
    have hℓC : IsUnit ((ℓ : ℕ) : C) := by
      have := (hunit (s j)).map δ
      rw [map_natCast] at this
      exact hℓunit this
    refine comp_pt'_eq_of_comp_ptF_eq hM ℓ hℓ hℓm L₀ πT pt' hiso hpb (hunit sS) (hunit (s j)) hℓC sS (s j)
      w Kw hKw (u j) (K j) (hK j) γ δ ?_ ?_
    · rw [← (ptF S sS w).2, ← Category.assoc, h, Category.assoc]
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
    have hk := key i (s j) (u j) (K j) (hK j) (Spec.preimage (w ≫ Limits.pullback.snd (ι i) (ι j))).hom
      (Spec.preimage (w ≫ Limits.pullback.fst (ι i) (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    refine (hk ?_).symm
    rw [hu j, hα, hβ]
    show (w ≫ _) ≫ (ι j ≫ V.ι) = (w ≫ _) ≫ (ι i ≫ V.ι)
    simp only [Category.assoc]
    rw [← Category.assoc (Limits.pullback.snd (ι i) (ι j)), ← Category.assoc (Limits.pullback.fst (ι i) (ι j)),
      Limits.pullback.condition]
  let Φ : VS ⟶ T := Scheme.Cover.glueMorphisms VS.affineCover φ hφ
  have hΦι : ∀ j, ι j ≫ Φ = φ j := fun j => Scheme.Cover.ι_glueMorphisms VS.affineCover φ hφ j

  have hprop : ∀ (S : Type) [CommRing S] (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (w : FakeEllipticCurve.WithFullLevel Λ N m S) (Kw : w.1.ExtraLevel ℓ) (x : Spec (CommRingCat.of S) ⟶ VS),
      x ≫ V.ι = (ptF S sS w).1 → Gen ℓ L₀ w Kw → (pt' S sS ⟨w.1, Kw⟩).1 = x ≫ Φ := by
    intro S _ sS w Kw x hx hKw
    refine Scheme.Cover.hom_ext (VS.affineCover.pullback₁ x) _ _ fun j => ?_
    change Limits.pullback.fst x (ι j) ≫ (pt' S sS ⟨w.1, Kw⟩).1 = Limits.pullback.fst x (ι j) ≫ (x ≫ Φ)
    refine Scheme.Cover.hom_ext (Limits.pullback x (ι j)).affineCover _ _ fun k => ?_
    let w' := (Limits.pullback x (ι j)).affineCover.f k
    show w' ≫ Limits.pullback.fst x (ι j) ≫ (pt' S sS ⟨w.1, Kw⟩).1 = w' ≫ Limits.pullback.fst x (ι j) ≫ (x ≫ Φ)
    have hγ : Spec.map (Spec.preimage (w' ≫ Limits.pullback.fst x (ι j))) = w' ≫ Limits.pullback.fst x (ι j) := Spec.map_preimage _
    have hδ : Spec.map (Spec.preimage (w' ≫ Limits.pullback.snd x (ι j))) = w' ≫ Limits.pullback.snd x (ι j) := Spec.map_preimage _
    rw [← Category.assoc, ← Category.assoc, ← hγ]
    have hk := key j sS w Kw hKw (Spec.preimage (w' ≫ Limits.pullback.fst x (ι j))).hom (Spec.preimage (w' ≫ Limits.pullback.snd x (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    have hc : Spec.map (Spec.preimage (w' ≫ Limits.pullback.fst x (ι j))) ≫ (ptF S sS w).1 =
        Spec.map (Spec.preimage (w' ≫ Limits.pullback.snd x (ι j))) ≫ y j := by
      rw [hγ, hδ, ← hx]
      show (w' ≫ _) ≫ (x ≫ V.ι) = (w' ≫ _) ≫ (ι j ≫ V.ι)
      simp only [Category.assoc]
      rw [← Category.assoc (Limits.pullback.fst x (ι j)), ← Category.assoc (Limits.pullback.snd x (ι j)),
        Limits.pullback.condition]
    have hk' := hk hc
    refine hk'.trans ?_
    show Spec.map (Spec.preimage (w' ≫ Limits.pullback.snd x (ι j))) ≫ φ j =
      Spec.map (Spec.preimage (w' ≫ Limits.pullback.fst x (ι j))) ≫ x ≫ Φ
    rw [← hΦι j, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [hγ, hδ]
    show (w' ≫ _) ≫ ι j = (w' ≫ _) ≫ x
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  refine ⟨Φ, ⟨?_, fun S _ sS w Kw x hx hKw => hprop S sS w Kw x hx hKw⟩, ?_⟩
  ·
    refine Scheme.Cover.hom_ext VS.affineCover _ _ fun j => ?_
    change (ι j ≫ Φ) ≫ πT = ι j ≫ V.ι ≫ πM
    rw [hΦι j]
    exact (pt' (A j) (s j) ⟨(u j).1, K j⟩).2
  ·
    rintro Φ' ⟨-, hΦ'⟩
    refine Scheme.Cover.hom_ext VS.affineCover _ _ fun j => ?_
    change ι j ≫ Φ' = ι j ≫ Φ
    rw [hΦι j]
    have := hΦ' (A j) (s j) (u j) (K j) (ι j) (by rw [hu j]) (hK j)
    exact this.symm

end ChartGlueT

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N m : ℕ} {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (V : M.Opens)
    (hV : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (w : FakeEllipticCurve.WithFullLevel Λ N m S),
      Set.range (ptF S s w).1 ⊆ (V : Set ↥M) ↔
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough w.1.lev
          (pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk))) →
        pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = w.1.L.one (geomPoint k sk))
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1) :
    ∃! Φ : (V : Scheme.{0}) ⟶ T, Φ ≫ πT = V.ι ≫ πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) (x : Spec (CommRingCat.of S) ⟶ (V : Scheme.{0})),
        x ≫ V.ι = (ptF S s w).1 →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        (pt' S s ⟨w.1, K⟩).1 = x ≫ Φ :=
  ChartGlueT.solution hB Λ hΛ hm' hM ℓ hℓ hℓm L₀ hL₀ hℓL₀ hL₀_left hL₀_index V hV T πT pt' hiso hpb

end S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptT_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_hom_ptT_comp_eq (solution)
