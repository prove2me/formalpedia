-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8cc443bc-98f0-5ff0-886e-86dd0d9d1efd

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

set_option maxHeartbeats 3200000

namespace B829A

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

variable {R : Type} [CommRing R]

@[reducible] def pointCommGroup {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { L.pointGroup t with mul_comm := fun x y => hc t x y }

theorem nsmulPt_eq_pow {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := pointCommGroup L hc t
    nsmulPt L t n P = P ^ n := by
  letI := pointCommGroup L hc t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem map_one_of_map_mul {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (G : SchemeHomOver t f → SchemeHomOver t f)
    (hG : ∀ P Q : SchemeHomOver t f, G (L.mul t P Q) = L.mul t (G P) (G Q)) :
    G (L.one t) = L.one t := by
  set a := G (L.one t) with ha
  have h2 : L.mul t a a = a := by rw [ha, ← hG, L.one_mul]
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t a) a := by rw [h2]
    _ = L.one t := L.inv_mul_cancel t a

theorem map_nsmulPt_of_map_mul {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (G : SchemeHomOver t f → SchemeHomOver t f)
    (hG : ∀ P Q : SchemeHomOver t f, G (L.mul t P Q) = L.mul t (G P) (G Q)) (n : ℕ) (P : SchemeHomOver t f) :
    G (nsmulPt L t n P) = nsmulPt L t n (G P) := by
  induction n with
  | zero => exact map_one_of_map_mul L G hG
  | succ n ih => simp only [nsmulPt, hG, ih]

section torsion
variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)

theorem nsmulPt_one (hc : L.IsCommutative) : nsmulPt L t n (L.one t) = L.one t := by
  letI := pointCommGroup L hc t
  rw [nsmulPt_eq_pow L hc]; exact one_pow n

theorem nsmulPt_mul_eq_one (hc : L.IsCommutative) {P Q : SchemeHomOver t f} (hP : nsmulPt L t n P = L.one t) (hQ : nsmulPt L t n Q = L.one t) :
    nsmulPt L t n (L.mul t P Q) = L.one t := by
  letI := pointCommGroup L hc t
  rw [nsmulPt_eq_pow L hc] at hP hQ ⊢
  show (P * Q) ^ n = 1
  rw [mul_pow]; exact (congrArg₂ (· * ·) hP hQ).trans (one_mul _)

theorem nsmulPt_inv_eq_one (hc : L.IsCommutative) {P : SchemeHomOver t f} (hP : nsmulPt L t n P = L.one t) :
    nsmulPt L t n (L.inv t P) = L.one t := by
  letI := pointCommGroup L hc t
  rw [nsmulPt_eq_pow L hc] at hP ⊢
  show (P⁻¹) ^ n = 1
  rw [inv_pow]; exact (congrArg (·⁻¹) hP).trans inv_one

theorem eq_one_of_nsmulPt_eq_one_of_coprime (hc : L.IsCommutative) {m : ℕ} (hnm : n.Coprime m) {P : SchemeHomOver t f}
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : P = L.one t := by
  letI := pointCommGroup L hc t
  rw [nsmulPt_eq_pow L hc] at hn hm
  have h1 : orderOf P ∣ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf P ∣ m := orderOf_dvd_of_pow_eq_one hm
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hnm h1 h2)

end torsion

end B829A

open B829A in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : S)) (E' : FakeEllipticCurve Λ (N * ℓ) S) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S, ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.1.lev P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.2.levK P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t) := by

  obtain ⟨CN, levN, hNc, hNfin, hNflat, hNfp, hNrank, hNchar⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit Λ S hu E' N (dvd_mul_right N ℓ)
  obtain ⟨CL, levL, hLc, hLfin, hLflat, hLfp, hLrank, hLchar⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit Λ S hu E' ℓ (dvd_mul_left ℓ N)
  have hk : ∀ (k : Type) [Field k] (sk : S →+* k), ((N * ℓ : ℕ) : k) ≠ 0 := by
    intro k _ sk
    have h := hu.map sk
    rw [map_natCast] at h
    exact h.ne_zero

  have htor_act : ∀ (n : ℕ) (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      nsmulPt E'.L t n P = E'.L.one t → nsmulPt E'.L t n (pushPt (E'.act x) (E'.act_over x) P) = E'.L.one t := by
    intro n x T t P hP
    rw [← map_nsmulPt_of_map_mul E'.L (fun Q => pushPt (E'.act x) (E'.act_over x) Q) (E'.act_hom x t) n P, hP,
      map_one_of_map_mul E'.L (fun Q => pushPt (E'.act x) (E'.act_over x) Q) (E'.act_hom x t)]

  let E : FakeEllipticCurve Λ N S :=
    { A := E'.A, f := E'.f, L := E'.L, comm := E'.comm, bundle := E'.bundle, dim_fibre := E'.dim_fibre,
      act := E'.act, act_over := E'.act_over, act_hom := E'.act_hom, act_one := E'.act_one, act_mul := E'.act_mul,
      act_add := E'.act_add, act_trace := E'.act_trace,
      C := CN, lev := levN, lev_closed := hNc,
      lev_sub := fun t P Q hP hQ => by
        obtain ⟨hP1, hP2⟩ := (hNchar t P).1 hP
        obtain ⟨hQ1, hQ2⟩ := (hNchar t Q).1 hQ
        exact ⟨(hNchar t _).2 ⟨(E'.lev_sub t P Q hP1 hQ1).1, nsmulPt_mul_eq_one E'.L t N E'.comm hP2 hQ2⟩,
          (hNchar t _).2 ⟨(E'.lev_sub t P Q hP1 hQ1).2, nsmulPt_inv_eq_one E'.L t N E'.comm hP2⟩⟩,
      lev_one := fun t => (hNchar t _).2 ⟨E'.lev_one t, nsmulPt_one E'.L t N E'.comm⟩,
      lev_torsion := fun t P hP => ((hNchar t P).1 hP).2,
      lev_stable := fun x {T} t P hP => by
        obtain ⟨hP1, hP2⟩ := (hNchar t P).1 hP
        exact (hNchar t _).2 ⟨E'.lev_stable x t P hP1, htor_act N x t P hP2⟩,
      lev_finite := hNfin, lev_flat := hNflat, lev_finitePresentation := hNfp, lev_rank := hNrank,
      lev_fibre := fun k _ _ sk hNk => by
        obtain ⟨e₀, he₀⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd Λ S E' N (dvd_mul_right N ℓ) k sk (hk k sk)
        refine ⟨e₀.trans (Equiv.subtypeEquivRight (fun P => (hNchar (geomPoint k sk) P).symm)), ?_⟩
        intro x y
        simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
        exact he₀ x y }

  let K : E.ExtraLevel ℓ :=
    { K := CL, levK := levL, levK_closed := hLc,
      levK_sub := fun t P Q hP hQ => by
        obtain ⟨hP1, hP2⟩ := (hLchar t P).1 hP
        obtain ⟨hQ1, hQ2⟩ := (hLchar t Q).1 hQ
        exact ⟨(hLchar t _).2 ⟨(E'.lev_sub t P Q hP1 hQ1).1, nsmulPt_mul_eq_one E'.L t ℓ E'.comm hP2 hQ2⟩,
          (hLchar t _).2 ⟨(E'.lev_sub t P Q hP1 hQ1).2, nsmulPt_inv_eq_one E'.L t ℓ E'.comm hP2⟩⟩,
      levK_one := fun t => (hLchar t _).2 ⟨E'.lev_one t, nsmulPt_one E'.L t ℓ E'.comm⟩,
      levK_torsion := fun t P hP => ((hLchar t P).1 hP).2,
      levK_stable := fun x {T} t P hP => by
        obtain ⟨hP1, hP2⟩ := (hLchar t P).1 hP
        exact (hLchar t _).2 ⟨E'.lev_stable x t P hP1, htor_act ℓ x t P hP2⟩,
      levK_disjoint := fun t P hPℓ hPN =>
        eq_one_of_nsmulPt_eq_one_of_coprime E'.L t N E'.comm hNℓ ((hNchar t P).1 hPN).2 ((hLchar t P).1 hPℓ).2,
      levK_finite := hLfin, levK_flat := hLflat, levK_finitePresentation := hLfp, levK_rank := hLrank,
      levK_fibre := fun k _ _ sk hℓk => by
        obtain ⟨e₀, he₀⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd Λ S E' ℓ (dvd_mul_left ℓ N) k sk (hk k sk)
        refine ⟨e₀.trans (Equiv.subtypeEquivRight (fun P => (hLchar (geomPoint k sk) P).symm)), ?_⟩
        intro x y
        simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
        exact he₀ x y }
  have hid : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E'.f),
      mapPt (Iso.refl E'.A).hom (Category.id_comp E'.f) P = P := by
    intro T t P; apply Subtype.ext; simp only [mapPt_coe, Iso.refl_hom, Category.comp_id]
  refine ⟨⟨E, K⟩, Iso.refl E'.A, Category.id_comp E'.f, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    show mapPt (Iso.refl E'.A).hom _ (E'.L.mul t P Q) = E'.L.mul t (mapPt _ _ P) (mapPt _ _ Q)
    rw [hid, hid, hid]
  · intro x
    show E'.act x ≫ 𝟙 E'.A = 𝟙 E'.A ≫ E'.act x
    rw [Category.comp_id, Category.id_comp]
  · intro T t P
    show FactorsThrough levN P ↔ _
    rw [hid]; exact hNchar t P
  · intro T t P
    show FactorsThrough levL P ↔ _
    rw [hid]; exact hLchar t P

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit (solution)
