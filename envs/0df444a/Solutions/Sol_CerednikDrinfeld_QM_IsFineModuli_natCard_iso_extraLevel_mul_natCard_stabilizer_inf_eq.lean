-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/78881da6-e9f4-5f2a-b3a7-6c7dd2a877fa

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_isReduced_K_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace STABAux

theorem isTwist_trans_iso {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type} [CommRing S] (c : ↥Λ)
    (u u' u'' : FakeEllipticCurve.WithFullLevel Λ N m S)
    (h₁ : FakeEllipticCurve.WithFullLevel.IsTwist c u u') (h₂ : FakeEllipticCurve.WithFullLevel.Iso u' u'') :
    FakeEllipticCurve.WithFullLevel.IsTwist c u u'' := by
  obtain ⟨e₁, he₁, hmul₁, hact₁, hlev₁, hP₁⟩ := h₁
  obtain ⟨e₂, he₂, hmul₂, hact₂, hlev₂, hP₂⟩ := h₂
  have he : (e₁ ≪≫ e₂).hom ≫ u''.1.f = u.1.f := by simp [he₁, he₂]
  have hmap : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt (e₁ ≪≫ e₂).hom he P = mapPt e₂.hom he₂ (mapPt e₁.hom he₁ P) := by
    intro T t P; apply Subtype.ext; simp [mapPt, Category.assoc]
  refine ⟨e₁ ≪≫ e₂, he, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [hmap, hmap, hmap, hmul₁, hmul₂]
  · intro x
    rw [Iso.trans_hom, ← Category.assoc, hact₁, Category.assoc, hact₂, Category.assoc]
  · intro T t P
    rw [hlev₁, hlev₂, hmap]
  · rw [hmap, hP₁, hP₂]

theorem iso_symm {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : FakeEllipticCurve.WithFullLevel.Iso u u') :
    FakeEllipticCurve.WithFullLevel.Iso u' u := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  have he' : e.inv ≫ u.1.f = u'.1.f := by rw [Iso.inv_comp_eq, he]
  have hround : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u'.1.f),
      mapPt e.hom he (mapPt e.inv he' P) = P := by
    intro T t P; apply Subtype.ext; simp [mapPt]
  have hround' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt e.inv he' (mapPt e.hom he P) = P := by
    intro T t P; apply Subtype.ext; simp [mapPt]
  refine ⟨e.symm, he', ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    show mapPt e.inv he' (u'.1.L.mul t P Q) = u.1.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    have := hmul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    rw [hround, hround] at this
    rw [← this, hround']
  · intro x
    show u'.1.act x ≫ e.inv = e.inv ≫ u.1.act x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hact, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro T t P
    show _ ↔ FactorsThrough u.1.lev (mapPt e.inv he' P)
    rw [hlev, hround]
  · show mapPt e.inv he' u'.2.P = u.2.P
    rw [← hP, hround']

theorem comp_eq_iff_isTwist {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (g : G) :
    (ptF S s u).1 ≫ (ρ g).hom = (ptF S s u).1 ↔ FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u u := by
  constructor
  · intro hg

    obtain ⟨y₁, hy₁⟩ := hρ.label_mul g g⁻¹
    obtain ⟨y₂, hy₂⟩ := hρ.label_mul g⁻¹ g
    obtain ⟨y₀, hy₀⟩ := hρ.label_one
    rw [mul_inv_cancel] at hy₁
    rw [inv_mul_cancel] at hy₂
    have hcd : ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
      refine ⟨y₀ - y₁, ?_⟩
      have : (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b]) - 1 =
          ((χ 1 : ℍ[ℚ, a, b]) - 1) - ((χ 1 : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b])) := by rw [sub_sub_sub_cancel_left]
      rw [this, hy₀, hy₁, Submodule.coe_sub, smul_sub]
    have hdc : ∃ y : ↥Λ, (χ g⁻¹ : ℍ[ℚ, a, b]) * (χ g : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
      refine ⟨y₀ - y₂, ?_⟩
      have : (χ g⁻¹ : ℍ[ℚ, a, b]) * (χ g : ℍ[ℚ, a, b]) - 1 =
          ((χ 1 : ℍ[ℚ, a, b]) - 1) - ((χ 1 : ℍ[ℚ, a, b]) - (χ g⁻¹ : ℍ[ℚ, a, b]) * (χ g : ℍ[ℚ, a, b])) := by rw [sub_sub_sub_cancel_left]
      rw [this, hy₀, hy₂, Submodule.coe_sub, smul_sub]
    obtain ⟨P', -, htw⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist hΛ u.1 u.2 (χ g) (χ g⁻¹) hcd hdc
    have htw' : FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u ⟨u.1, P'⟩ := by
      obtain ⟨E, P⟩ := u
      exact htw
    have h1 := hρ.twist g S s u ⟨u.1, P'⟩ htw'
    rw [hg] at h1
    have h2 : ptF S s ⟨u.1, P'⟩ = ptF S s u := Subtype.ext h1
    have h3 := hM.ptF_injective S s ⟨u.1, P'⟩ u h2
    exact isTwist_trans_iso (χ g) u ⟨u.1, P'⟩ u htw' h3
  · intro h
    exact (hρ.twist g S s u u h).symm

section beta

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem pushPt_act_pushPt_act (E : FakeEllipticCurve Λ N S) (x y : ↥Λ)
    (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) Q) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) Q := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [E.act_mul x y h]

theorem mapPt_pushPt_act (E' E : FakeEllipticCurve Λ N S) (φ : E'.A ⟶ E.A) (hφ : φ ≫ E.f = E'.f)
    (hact : ∀ x : ↥Λ, E'.act x ≫ φ = φ ≫ E.act x) (x : ↥Λ)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E'.f) :
    mapPt φ hφ (pushPt (E'.act x) (E'.act_over x) Q) = pushPt (E.act x) (E.act_over x) (mapPt φ hφ Q) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [hact]

theorem mapPt_one (E' E : FakeEllipticCurve Λ N S) (φ : E'.A ⟶ E.A) (hφ : φ ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt φ hφ (E'.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    mapPt φ hφ (E'.L.one t) = E.L.one t := by
  have h := hmul t (E'.L.one t) (E'.L.one t)
  rw [E'.L.one_mul] at h
  letI := E.L.pointGroup t
  have h' : mapPt φ hφ (E'.L.one t) * mapPt φ hφ (E'.L.one t) = mapPt φ hφ (E'.L.one t) := h.symm
  exact mul_eq_left.mp h'

theorem mapPt_nsmulPt (E' E : FakeEllipticCurve Λ N S) (φ : E'.A ⟶ E.A) (hφ : φ ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt φ hφ (E'.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E'.f) :
    mapPt φ hφ (nsmulPt E'.L t n P) = nsmulPt E.L t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one E' E φ hφ hmul t
  | succ n ih =>
    show mapPt φ hφ (E'.L.mul t (nsmulPt E'.L t n P) P) = E.L.mul t (nsmulPt E.L t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hmul, ih]

theorem pushPt_act_nsmulPt (E : FakeEllipticCurve Λ N S) (x : ↥Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n P) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) :=
  mapPt_nsmulPt E E (E.act x) (E.act_over x) (fun t P Q => E.act_hom x t P Q) t n P

theorem mapPt_sectionAt (E' E : FakeEllipticCurve Λ N S) (φ : E'.A ⟶ E.A) (hφ : φ ≫ E.f = E'.f)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E'.f) (k : Type) [Field k] (sk : S →+* k) :
    mapPt φ hφ (FakeEllipticCurve.sectionAt P k sk) = FakeEllipticCurve.sectionAt (mapPt φ hφ P) k sk := by
  apply Subtype.ext
  simp only [mapPt_coe, FakeEllipticCurve.sectionAt, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

theorem pushPt_act_sectionAt_eq_of_sub_mem {m : ℕ} (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x y : ↥Λ)
    (hxy : ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b])) :
    pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P.P k sk) =
      pushPt (E.act y) (E.act_over y) (FakeEllipticCurve.sectionAt P.P k sk) := by
  have hann := (P.annihilator k sk (x - y)).mpr (by simpa using hxy)
  have hx : x = (x - y) + y := (sub_add_cancel x y).symm
  conv_lhs => rw [hx]
  rw [E.act_add (x - y) y, hann, E.L.one_mul]

end beta

section gamma

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [QuaternionAlgebra.coe_natCast, zsmul_eq_mul, Int.cast_natCast, mul_one]
  rw [this]
  exact Λ.smul_mem _ hΛ.one_mem

theorem geomPoint_id (k : Type) [Field k] : geomPoint k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by
  simp [geomPoint]

theorem smul_mem_line {ℓ m : ℕ} (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) (w : ↥Λ) :
    (m : ℚ) • (w : ℍ[ℚ, a, b]) ∈ L₀ := by
  obtain ⟨c, rfl⟩ := hℓm
  have hw : ((c : ℕ) : ℤ) • (w : ℍ[ℚ, a, b]) ∈ Λ := Λ.smul_mem _ w.2
  have h := hℓL₀ ⟨((c : ℕ) : ℤ) • (w : ℍ[ℚ, a, b]), hw⟩
  have : (((ℓ * c : ℕ) : ℚ)) • (w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (((c : ℕ) : ℤ) • (w : ℍ[ℚ, a, b])) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring_nf
  rw [this]; exact h

variable {N : ℕ} {S : Type} [CommRing S]

theorem pushPt_act_pushPt_act' (E : FakeEllipticCurve Λ N S) (x y : ↥Λ)
    (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) Q) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) Q := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]
  rw [E.act_mul x y h]

theorem pushPt_act_nsmulPt_sectionAt_eq_one_iff (hΛ : IsOrder Λ) {m : ℕ} (hm : m ≠ 0)
    (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (y : ↥Λ) :
    pushPt (E.act y) (E.act_over y) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
        E.L.one (geomPoint k sk) ↔
      ∃ z : ↥Λ, (y : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by
  have hn := natCast_mem hΛ (m / ℓ)
  rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hΛ.one_mem (m / ℓ) hn,
    pushPt_act_pushPt_act' E y ⟨_, hn⟩ (hΛ.mul_mem y.2 hn), P.annihilator k sk]
  obtain ⟨c, hc⟩ := hℓm
  have hc' : c ≠ 0 := by rintro rfl; simp at hc; exact hm hc
  have hdiv : m / ℓ = c := by rw [hc, Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hℓ)]
  have hcQ : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc'

  have hprod : ((y : ℍ[ℚ, a, b]) * (((m / ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b])) = (c : ℚ) • (y : ℍ[ℚ, a, b]) := by
    rw [QuaternionAlgebra.mul_coe_eq_smul, hdiv]
  simp only [Submodule.coe_mk]
  rw [hprod]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : (y : ℍ[ℚ, a, b]) = (c : ℚ)⁻¹ • ((m : ℚ) • (z : ℍ[ℚ, a, b])) := by
      rw [← hz, smul_smul, inv_mul_cancel₀ hcQ, one_smul]
    rw [this, smul_smul, hc]; push_cast
    rw [mul_comm ((ℓ : ℚ)) (c : ℚ), ← mul_assoc, inv_mul_cancel₀ hcQ, one_mul]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hz, smul_smul, hc]; push_cast
    rw [mul_comm]

end gamma

section delta

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem factorsThrough_iff_of_val_eq {A C T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (lev : C ⟶ A)
    {t t' : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) (P' : SchemeHomOver t' f) (h : P.1 = P'.1) :
    FactorsThrough lev P ↔ FactorsThrough lev P' := by
  unfold FactorsThrough; rw [h]

theorem pushPt_act_eq_of_sub (E : FakeEllipticCurve Λ N S) (y y' : ↥Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f)
    (h : pushPt (E.act (y - y')) (E.act_over _) Q = E.L.one t) :
    pushPt (E.act y) (E.act_over y) Q = pushPt (E.act y') (E.act_over y') Q := by
  have hy : y = (y - y') + y' := (sub_add_cancel y y').symm
  conv_lhs => rw [hy]
  rw [E.act_add (y - y') y' t Q, h, E.L.one_mul]

theorem pushPt_act_sub_eq_one_of_eq (E : FakeEllipticCurve Λ N S) (y y' : ↥Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f)
    (h : pushPt (E.act y) (E.act_over y) Q = pushPt (E.act y') (E.act_over y') Q) :
    pushPt (E.act (y - y')) (E.act_over _) Q = E.L.one t := by
  have hy : y = (y - y') + y' := (sub_add_cancel y y').symm
  have h2 : pushPt (E.act ((y - y') + y')) (E.act_over _) Q = pushPt (E.act y') (E.act_over y') Q := by
    rw [← hy]; exact h
  rw [E.act_add (y - y') y' t Q] at h2
  letI := E.L.pointGroup t
  exact mul_eq_right.mp h2

theorem pushPt_act_Q0_eq_iff (hΛ : IsOrder Λ) {m : ℕ} (hm : m ≠ 0)
    (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (y y' : ↥Λ) :
    pushPt (E.act y) (E.act_over y) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
      pushPt (E.act y') (E.act_over y') (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) ↔
      ∃ z : ↥Λ, (y : ℍ[ℚ, a, b]) - (y' : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by
  have key := pushPt_act_nsmulPt_sectionAt_eq_one_iff hΛ hm E P ℓ hℓ hℓm k sk (y - y')
  rw [Submodule.coe_sub] at key
  constructor
  · intro h; exact key.mp (pushPt_act_sub_eq_one_of_eq E y y' _ _ h)
  · intro h; exact pushPt_act_eq_of_sub E y y' _ _ (key.mpr h)

variable {G : Type} [Group G]

theorem chi_mul_chi_inv {m : ℕ} (χ : G → ↥Λ)
    (label_one : ∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (label_mul : ∀ g g' : G,
      ∃ y : ↥Λ, (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (g : G) : ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  obtain ⟨y₁, hy₁⟩ := label_mul g g⁻¹
  obtain ⟨y₀, hy₀⟩ := label_one
  rw [mul_inv_cancel] at hy₁
  refine ⟨y₀ - y₁, ?_⟩
  have : (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b]) - 1 =
      ((χ 1 : ℍ[ℚ, a, b]) - 1) - ((χ 1 : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b])) := by
    rw [sub_sub_sub_cancel_left]
  rw [this, hy₀, hy₁, Submodule.coe_sub, smul_sub]

theorem exists_line_of_mem (hΛ : IsOrder Λ) {m : ℕ} (hm : m ≠ 0)
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m)
    (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (χ : G → ↥Λ)
    (label_mul : ∀ g g' : G,
      ∃ y : ↥Λ, (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)
    (g₁ g₂ : G) (h12 : g₁ * g₂⁻¹ ∈ H) (x : ↥Λ) (hx : (x : ℍ[ℚ, a, b]) ∈ L₀) :
    ∃ x' : ↥Λ, (x' : ℍ[ℚ, a, b]) ∈ L₀ ∧
      pushPt (E.act x') (E.act_over x') (pushPt (E.act (χ g₂)) (E.act_over (χ g₂))
        (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act (χ g₁)) (E.act_over (χ g₁))
        (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) := by
  have hx' : (x : ℍ[ℚ, a, b]) * (χ (g₁ * g₂⁻¹) : ℍ[ℚ, a, b]) ∈ L₀ := (hH _).mp h12 x hx
  refine ⟨⟨(x : ℍ[ℚ, a, b]) * (χ (g₁ * g₂⁻¹) : ℍ[ℚ, a, b]), hL₀ hx'⟩, hx', ?_⟩
  rw [pushPt_act_pushPt_act' E _ _ (hΛ.mul_mem (hL₀ hx') (χ g₂).2),
    pushPt_act_pushPt_act' E _ _ (hΛ.mul_mem x.2 (χ g₁).2),
    pushPt_act_Q0_eq_iff hΛ hm E P ℓ hℓ hℓm k (RingHom.id k)]
  obtain ⟨w, hw⟩ := label_mul (g₁ * g₂⁻¹) g₂
  rw [inv_mul_cancel_right] at hw

  obtain ⟨c, hc⟩ := hℓm
  refine ⟨⟨-(((c : ℕ) : ℤ) • ((x : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]))), Λ.neg_mem (Λ.smul_mem _ (hΛ.mul_mem x.2 w.2))⟩, ?_⟩
  simp only [Submodule.coe_mk]
  have e1 : (x : ℍ[ℚ, a, b]) * (χ (g₁ * g₂⁻¹) : ℍ[ℚ, a, b]) * (χ g₂ : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (χ g₁ : ℍ[ℚ, a, b]) =
      -((x : ℍ[ℚ, a, b]) * ((χ g₁ : ℍ[ℚ, a, b]) - (χ (g₁ * g₂⁻¹) : ℍ[ℚ, a, b]) * (χ g₂ : ℍ[ℚ, a, b]))) := by
    rw [mul_sub, mul_assoc]; abel
  rw [e1, hw, hc]
  push_cast
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, smul_neg, smul_smul, ← mul_smul_comm]

end delta

section delta2

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {G : Type} [Group G]

theorem mem_of_forall_exists (hΛ : IsOrder Λ) {m : ℕ} (hm : m ≠ 0)
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m)
    (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (χ : G → ↥Λ)
    (label_one : ∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (label_mul : ∀ g g' : G,
      ∃ y : ↥Λ, (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)
    (g g' : G)
    (h : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ → ∃ x' : ↥Λ, (x' : ℍ[ℚ, a, b]) ∈ L₀ ∧
      pushPt (E.act x') (E.act_over x') (pushPt (E.act (χ g')) (E.act_over (χ g'))
        (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act (χ g)) (E.act_over (χ g))
        (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))))) :
    g * g'⁻¹ ∈ H := by
  rw [hH]
  intro x₀ hx₀
  obtain ⟨x', hx'L, heq⟩ := h ⟨x₀, hL₀ hx₀⟩ hx₀
  rw [pushPt_act_pushPt_act' E _ _ (hΛ.mul_mem (hL₀ hx'L) (χ g').2),
    pushPt_act_pushPt_act' E _ _ (hΛ.mul_mem (hL₀ hx₀) (χ g).2),
    pushPt_act_Q0_eq_iff hΛ hm E P ℓ hℓ hℓm k (RingHom.id k)] at heq
  obtain ⟨z, hz⟩ := heq
  simp only [Submodule.coe_mk] at hz
  obtain ⟨w₂, hw₂⟩ := label_mul g g'⁻¹
  obtain ⟨w, hw⟩ := chi_mul_chi_inv χ label_one label_mul g'
  have e2 : (χ (g * g'⁻¹) : ℍ[ℚ, a, b]) = (χ g : ℍ[ℚ, a, b]) * (χ g'⁻¹ : ℍ[ℚ, a, b]) + (m : ℚ) • (w₂ : ℍ[ℚ, a, b]) := by
    rw [← hw₂]; abel
  have e3 : x₀ * (χ g : ℍ[ℚ, a, b]) = (x' : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) - (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by
    rw [← hz]; abel
  have e4 : (χ g' : ℍ[ℚ, a, b]) * (χ g'⁻¹ : ℍ[ℚ, a, b]) = 1 + (m : ℚ) • (w : ℍ[ℚ, a, b]) := by
    rw [← hw]; abel
  have key : x₀ * (χ (g * g'⁻¹) : ℍ[ℚ, a, b]) =
      (x' : ℍ[ℚ, a, b]) + (m : ℚ) • ((x' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]))
        - (ℓ : ℚ) • ((z : ℍ[ℚ, a, b]) * (χ g'⁻¹ : ℍ[ℚ, a, b])) + (m : ℚ) • (x₀ * (w₂ : ℍ[ℚ, a, b])) := by
    rw [e2, mul_add, mul_smul_comm, ← mul_assoc, e3, sub_mul, smul_mul_assoc, mul_assoc, e4, mul_add, mul_one,
      mul_smul_comm]
  rw [key]
  refine L₀.add_mem (L₀.sub_mem (L₀.add_mem hx'L ?_) ?_) ?_
  · exact smul_mem_line hℓm L₀ hℓL₀ ⟨_, hΛ.mul_mem (hL₀ hx'L) w.2⟩
  · exact hℓL₀ ⟨_, hΛ.mul_mem z.2 (χ g'⁻¹).2⟩
  · exact smul_mem_line hℓm L₀ hℓL₀ ⟨_, hΛ.mul_mem (hL₀ hx₀) w₂.2⟩

end delta2

section s3

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem pushPt_act_one (hΛ : IsOrder Λ) {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) Q = Q := by
  apply Subtype.ext; simp only [mapPt_coe]; rw [E.act_one hΛ.one_mem]; exact Category.comp_id _

theorem pushPt_act_sectionAt {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (x : ↥Λ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type) [Field k] (sk : S →+* k) :
    pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) =
      FakeEllipticCurve.sectionAt (pushPt (E.act x) (E.act_over x) P) k sk :=
  mapPt_sectionAt E E (E.act x) (E.act_over x) P k sk

theorem exists_index_line (hΛ : IsOrder Λ) {m : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m) (ℓ : ℕ)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) (K : Fin n → E.ExtraLevel ℓ)
    (hKexh : ∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x)
    (i₀ : Fin n)
    (hK₀ : ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough (K i₀).levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) = Q)
    (c d : ↥Λ) (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (htw : FakeEllipticCurve.WithFullLevel.IsTwist d (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩) :
    ∃ i : Fin n, ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough (K i).levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) = Q := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := htw
  dsimp only at he hmul hact hlev hP

  obtain ⟨K', hK'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff ℓ E E e he
    (fun t P Q => hmul t P Q) hact (fun t P => hlev t P) (K i₀)
  obtain ⟨i, hi⟩ := hKexh K'
  refine ⟨i, fun Q => ?_⟩

  let x₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f := ⟨Q.1, by rw [← geomPoint_id]; exact Q.2⟩
  rw [← factorsThrough_iff_of_val_eq (K i).levK x₁ Q rfl, ← hi x₁, factorsThrough_iff_of_val_eq K'.levK x₁ Q rfl]

  have he' : e.inv ≫ E.f = E.f := by rw [Iso.inv_comp_eq, he]
  have hround : mapPt e.hom he (mapPt e.inv he' Q) = Q := by apply Subtype.ext; simp [mapPt]
  rw [← hround, hK', hK₀]

  set Pk := FakeEllipticCurve.sectionAt P.P k (RingHom.id k) with hPk
  have hcd1 : pushPt (E.act ⟨(c : ℍ[ℚ,a,b]) * (d : ℍ[ℚ,a,b]), hΛ.mul_mem c.2 d.2⟩) (E.act_over _) Pk = Pk := by
    rw [hPk, pushPt_act_sectionAt_eq_of_sub_mem E P k (RingHom.id k) ⟨_, hΛ.mul_mem c.2 d.2⟩ ⟨1, hΛ.one_mem⟩
      (by simpa using hcd), pushPt_act_one hΛ]
  have heP : mapPt e.hom he Pk = pushPt (E.act c) (E.act_over c) Pk := by
    conv_lhs => rw [← hcd1, ← pushPt_act_pushPt_act' E c d (hΛ.mul_mem c.2 d.2)]
    rw [mapPt_pushPt_act E E e.hom he hact, hPk, pushPt_act_sectionAt, mapPt_sectionAt E E e.hom he, hP]

  have hmove : ∀ x : ↥Λ, mapPt e.hom he (pushPt (E.act x) (E.act_over x) (nsmulPt E.L _ (m / ℓ) Pk)) =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c) (nsmulPt E.L _ (m / ℓ) Pk)) := by
    intro x
    rw [mapPt_pushPt_act E E e.hom he hact, mapPt_nsmulPt E E e.hom he (fun t P Q => hmul t P Q), heP,
      ← pushPt_act_nsmulPt]
  constructor
  · rintro ⟨x, hx, hxe⟩
    refine ⟨x, hx, ?_⟩
    rw [← hmove x, hxe]
  · rintro ⟨x, hx, hxe⟩
    refine ⟨x, hx, ?_⟩

    have : mapPt e.hom he (pushPt (E.act x) (E.act_over x) (nsmulPt E.L _ (m / ℓ) Pk)) = Q := by rw [hmove x, hxe, hround]
    rw [← this]
    apply Subtype.ext; simp [mapPt]

end s3

section s2

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem factorsThrough_levK_of_forall_points (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    {ℓ : ℕ} (hℓk : (ℓ : k) ≠ 0) (K K' : E.ExtraLevel ℓ)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK x → FactorsThrough K'.levK x)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E.f) (hQ : FactorsThrough K.levK Q) :
    FactorsThrough K'.levK Q := by
  haveI : IsReduced K.K := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero k E K hℓk
  haveI : IsClosedImmersion K'.levK := K'.levK_closed
  haveI : IsFinite (K.levK ≫ E.f) := K.levK_finite
  haveI : LocallyOfFiniteType (K.levK ≫ E.f) := inferInstance

  obtain ⟨φ₀, hφ₀⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k (K.levK ≫ E.f) E.f K'.levK
    K.levK rfl (fun z => h (mapPt K.levK rfl z) ⟨z.1, rfl⟩)
  obtain ⟨Q₀, hQ₀⟩ := hQ
  exact ⟨Q₀ ≫ φ₀, by rw [Category.assoc, hφ₀, hQ₀]⟩

theorem inv_clauses {S : Type} [CommRing S] (E' E : FakeEllipticCurve Λ N S) (e : E'.A ≅ E.A) (he : e.hom ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt e.hom he (E'.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E'.act x ≫ e.hom = e.hom ≫ E.act x) :
    ∃ he' : e.inv ≫ E'.f = E.f,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt e.inv he' (E.L.mul t P Q) = E'.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ e.inv = e.inv ≫ E'.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f), mapPt e.hom he (mapPt e.inv he' P) = P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f), mapPt e.inv he' (mapPt e.hom he P) = P) := by
  have he' : e.inv ≫ E'.f = E.f := by rw [Iso.inv_comp_eq, he]
  have hround : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt e.hom he (mapPt e.inv he' P) = P := by intro T t P; apply Subtype.ext; simp [mapPt]
  have hround' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      mapPt e.inv he' (mapPt e.hom he P) = P := by intro T t P; apply Subtype.ext; simp [mapPt]
  refine ⟨he', ?_, ?_, hround, hround'⟩
  · intro T t P Q
    have := hmul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    rw [hround, hround] at this
    rw [← this, hround']
  · intro x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hact, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end s2

section s2b

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem nsmulPt_sectionAt {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type) [Field k] (sk : S →+* k) (n : ℕ) :
    FakeEllipticCurve.sectionAt (nsmulPt E.L (𝟙 _) n P) k sk = nsmulPt E.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt P k sk) := by
  induction n with
  | zero => exact E.L.one_natural _ _ _ _
  | succ n ih =>
    show schemeHomOverComp (geomPoint k sk) _ (E.L.mul _ (nsmulPt E.L (𝟙 _) n P) P) = E.L.mul _ _ _
    rw [E.L.mul_natural, ← ih]; rfl

theorem sectionAt_id_val {S : Type} [Field S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    (FakeEllipticCurve.sectionAt P S (RingHom.id S)).1 = P.1 := by
  show geomPoint S (RingHom.id S) ≫ P.1 = P.1
  rw [geomPoint_id, Category.id_comp]

theorem eq_of_sectionAt_id_eq {S : Type} [Field S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (P P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (h : FakeEllipticCurve.sectionAt P S (RingHom.id S) = FakeEllipticCurve.sectionAt P' S (RingHom.id S)) : P = P' := by
  apply Subtype.ext
  rw [← sectionAt_id_val P, ← sectionAt_id_val P', h]

theorem iso_of_line (hΛ : IsOrder Λ) {m : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m)
    (ℓ : ℕ) (hℓk : (ℓ : k) ≠ 0) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (Ki K₀ : E.ExtraLevel ℓ)
    (hK₀ : ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough K₀.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) = Q)
    (c : ↥Λ)
    (hKi : ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough Ki.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) = Q)
    (htw : FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩) :
    FakeEllipticCurve.WithExtraLevel.Iso (⟨E, Ki⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K₀⟩ := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := htw
  dsimp only at he hmul hact hlev hP
  obtain ⟨K, hK⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff ℓ E E e he
    (fun t P Q => hmul t P Q) hact (fun t P => hlev t P) Ki
  obtain ⟨he', hmul', hact', hround, hround'⟩ := inv_clauses E E e he (fun t P Q => hmul t P Q) hact
  set Pk := FakeEllipticCurve.sectionAt P.P k (RingHom.id k) with hPk
  have heP : mapPt e.hom he (pushPt (E.act c) (E.act_over c) Pk) = Pk := by
    rw [hPk, pushPt_act_sectionAt, mapPt_sectionAt E E e.hom he, hP]

  have hmove : ∀ x : ↥Λ, mapPt e.hom he (pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
      (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) Pk))) =
      pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) Pk) := by
    intro x
    rw [pushPt_act_nsmulPt E c, mapPt_pushPt_act E E e.hom he hact, mapPt_nsmulPt E E e.hom he (fun t P Q => hmul t P Q), heP]

  have hKK₀ : ∀ Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f, FactorsThrough K.levK Q ↔ FactorsThrough K₀.levK Q := by
    intro Q
    rw [← hround _ Q, hK, hKi, hK₀, hround]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hmove x, hxe, hround]
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hxe, ← hmove x, hround']
  have h1 : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK x → FactorsThrough K₀.levK x := by
    intro x hx
    let Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f := ⟨x.1, by rw [geomPoint_id]; exact x.2⟩
    exact (factorsThrough_iff_of_val_eq K₀.levK x Q rfl).mpr ((hKK₀ Q).mp ((factorsThrough_iff_of_val_eq K.levK x Q rfl).mp hx))
  have h2 : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K₀.levK x → FactorsThrough K.levK x := by
    intro x hx
    let Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f := ⟨x.1, by rw [geomPoint_id]; exact x.2⟩
    exact (factorsThrough_iff_of_val_eq K.levK x Q rfl).mpr ((hKK₀ Q).mpr ((factorsThrough_iff_of_val_eq K₀.levK x Q rfl).mp hx))
  refine ⟨e, he, fun t P Q => hmul t P Q, hact, fun t P => hlev t P, ?_⟩
  intro T t Q
  show FactorsThrough Ki.levK Q ↔ FactorsThrough K₀.levK (mapPt e.hom he Q)
  rw [← hK]
  exact ⟨fun h => factorsThrough_levK_of_forall_points k E hℓk K K₀ h1 t _ h,
    fun h => factorsThrough_levK_of_forall_points k E hℓk K₀ K h2 t _ h⟩

end s2b

section s2c

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem exists_of_iso (hΛ : IsOrder Λ) {m : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m)
    (ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (Ki K₀ : E.ExtraLevel ℓ)
    (hK₀ : ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough K₀.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) = Q)
    (hiso : FakeEllipticCurve.WithExtraLevel.Iso (⟨E, Ki⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K₀⟩) :
    ∃ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩ ∧
      ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough Ki.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
            (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) = Q := by
  obtain ⟨e, he, hmul, hact, hlev, hlevK⟩ := hiso
  dsimp only at he hmul hact hlev hlevK
  obtain ⟨he', hmul', hact', hround, hround'⟩ := inv_clauses E E e he (fun t P Q => hmul t P Q) hact
  set Pk := FakeEllipticCurve.sectionAt P.P k (RingHom.id k) with hPk

  have hPtors : nsmulPt E.L (geomPoint k (RingHom.id k)) m Pk = E.L.one _ := by
    rw [hPk, ← nsmulPt_sectionAt, P.torsion]; exact E.L.one_natural _ _ _ _
  have htors_inv : nsmulPt E.L (geomPoint k (RingHom.id k)) m (mapPt e.inv he' Pk) = E.L.one _ := by
    rw [← mapPt_nsmulPt E E e.inv he' (fun t P Q => hmul' t P Q), hPtors, mapPt_one E E e.inv he' (fun t P Q => hmul' t P Q)]
  have htors_hom : nsmulPt E.L (geomPoint k (RingHom.id k)) m (mapPt e.hom he Pk) = E.L.one _ := by
    rw [← mapPt_nsmulPt E E e.hom he (fun t P Q => hmul t P Q), hPtors, mapPt_one E E e.hom he (fun t P Q => hmul t P Q)]
  obtain ⟨c, hc⟩ := P.generates k (RingHom.id k) (mapPt e.inv he' Pk) htors_inv
  obtain ⟨c', hc'⟩ := P.generates k (RingHom.id k) (mapPt e.hom he Pk) htors_hom
  rw [← hPk] at hc hc'

  have hecP : mapPt e.hom he (pushPt (E.act c) (E.act_over c) Pk) = Pk := by rw [hc, hround]

  have hcc' : pushPt (E.act ⟨(c : ℍ[ℚ,a,b]) * (c' : ℍ[ℚ,a,b]), hΛ.mul_mem c.2 c'.2⟩) (E.act_over _) Pk =
      pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) Pk := by
    rw [← pushPt_act_pushPt_act' E c c', hc', ← mapPt_pushPt_act E E e.hom he hact, hc, hround, pushPt_act_one hΛ]
  have hc'c : pushPt (E.act ⟨(c' : ℍ[ℚ,a,b]) * (c : ℍ[ℚ,a,b]), hΛ.mul_mem c'.2 c.2⟩) (E.act_over _) Pk =
      pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) Pk := by
    rw [← pushPt_act_pushPt_act' E c' c, hc, ← mapPt_pushPt_act E E e.inv he' hact', hc', hround', pushPt_act_one hΛ]
  have hunit : ∀ (u : ↥Λ), pushPt (E.act u) (E.act_over u) Pk = pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) Pk →
      ∃ y : ↥Λ, (u : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro u hu
    have h1 := pushPt_act_sub_eq_one_of_eq E u ⟨1, hΛ.one_mem⟩ _ Pk hu
    rw [hPk] at h1
    obtain ⟨y, hy⟩ := (P.annihilator k (RingHom.id k) (u - ⟨1, hΛ.one_mem⟩)).mp h1
    exact ⟨y, by simpa using hy⟩
  refine ⟨c, c', hunit _ hcc', hunit _ hc'c, ?_, ?_⟩
  ·
    refine ⟨e, he, fun t P Q => hmul t P Q, hact, fun t P => hlev t P, ?_⟩
    show mapPt e.hom he (pushPt (E.act c) (E.act_over c) P.P) = P.P
    apply eq_of_sectionAt_id_eq
    rw [← mapPt_sectionAt E E e.hom he, ← pushPt_act_sectionAt, ← hPk, hecP]
  · intro Q
    rw [hlevK, hK₀]
    have hmove : ∀ x : ↥Λ, mapPt e.inv he' (pushPt (E.act x) (E.act_over x)
        (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) Pk)) =
        pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) Pk)) := by
      intro x
      rw [mapPt_pushPt_act E E e.inv he' hact', mapPt_nsmulPt E E e.inv he' (fun t P Q => hmul' t P Q), ← hc,
        ← pushPt_act_nsmulPt]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hmove x, hxe, hround']
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hxe, ← hmove x, hround]

end s2c

section helpers

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem pushPt_act_P_eq_of_sub_mem {m : ℕ} (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (P : E.FullLevel m) (x y : ↥Λ)
    (hxy : ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b])) :
    pushPt (E.act x) (E.act_over x) P.P = pushPt (E.act y) (E.act_over y) P.P := by
  apply eq_of_sectionAt_id_eq
  rw [← pushPt_act_sectionAt, ← pushPt_act_sectionAt, pushPt_act_sectionAt_eq_of_sub_mem E P k (RingHom.id k) x y hxy]

theorem pushPt_act_Q0_eq_of_sub_mem {m : ℕ} (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (P : E.FullLevel m) (ℓ : ℕ) (x y : ↥Λ)
    (hxy : ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b])) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) =
    pushPt (E.act y) (E.act_over y) (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) := by
  rw [pushPt_act_nsmulPt, pushPt_act_nsmulPt, pushPt_act_sectionAt_eq_of_sub_mem E P k (RingHom.id k) x y hxy]

theorem isTwist_of_sub_mem {m : ℕ} (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (P : E.FullLevel m) (x y : ↥Λ)
    (hxy : ∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) - (y : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b]))
    (h : FakeEllipticCurve.WithFullLevel.IsTwist y (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩) :
    FakeEllipticCurve.WithFullLevel.IsTwist x (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩ := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  refine ⟨e, he, hmul, hact, hlev, ?_⟩
  dsimp only at hP ⊢
  rw [pushPt_act_P_eq_of_sub_mem k E P x y hxy, hP]

end helpers

end STABAux

open STABAux in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)

    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (n : ℕ) (K : Fin n → u.1.ExtraLevel ℓ)
    (hKdist : ∀ i j : Fin n,
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j)
    (hKexh : ∀ K' : u.1.ExtraLevel ℓ, ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x)

    (i₀ : Fin n)
    (hK₀ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) u.1.f),
      FactorsThrough (K i₀).levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k' sk)) = Q) :
    Nat.card {i : Fin n // FakeEllipticCurve.WithExtraLevel.Iso
        (⟨u.1, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨u.1, K i₀⟩} *
      Nat.card {g : G // g ∈ H ∧ (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} =
    Nat.card {g : G // (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨E, P⟩ := u
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero

  have hmk : (m : k) ≠ 0 := by
    let φ : 𝒪 →+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom)
    have := (hm'.map φ)
    rw [map_natCast] at this
    exact this.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; exact hmk (by simp)
  have hℓk : (ℓ : k) ≠ 0 := by
    obtain ⟨c, hc⟩ := hℓm
    intro h; apply hmk; rw [hc]; push_cast; rw [h, zero_mul]

  let inS : G → Prop := fun g =>
    (ptF k s ⟨E, P⟩).1 ≫ (ρ g).hom = (ptF k s ⟨E, P⟩).1
  let Q₀ := nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))
  let line : ↥Λ → E.ExtraLevel ℓ → Prop := fun c K' =>
    ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough K'.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)))) = Q
  have hK₀' : ∀ (Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f), FactorsThrough (K i₀).levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k (RingHom.id k)) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k))) = Q :=
    hK₀ k (RingHom.id k)

  have hS_one : inS 1 := by
    show (ptF k s ⟨E, P⟩).1 ≫ (ρ 1).hom = (ptF k s ⟨E, P⟩).1
    rw [map_one]; exact Category.comp_id _
  have hS_mul : ∀ g g', inS g → inS g' → inS (g * g') := by
    intro g g' hg hg'
    show (ptF k s ⟨E, P⟩).1 ≫ (ρ (g * g')).hom = (ptF k s ⟨E, P⟩).1
    rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, ← Category.assoc, hg', hg]
  have hS_inv : ∀ g, inS g → inS g⁻¹ := by
    intro g hg
    change (ptF k s ⟨E, P⟩).1 ≫ (ρ g).hom = (ptF k s ⟨E, P⟩).1 at hg
    show (ptF k s ⟨E, P⟩).1 ≫ (ρ g⁻¹).hom = (ptF k s ⟨E, P⟩).1
    have h2 := congrArg (· ≫ (ρ g).inv) hg
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
    rw [map_inv, Aut.Aut_inv_def]
    exact h2.symm
  have hS_tw : ∀ g, inS g ↔ FakeEllipticCurve.WithFullLevel.IsTwist (χ g) (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P⟩ :=
    fun g => comp_eq_iff_isTwist hΛo hM hρ k s ⟨E, P⟩ g

  have hrange : ∀ i : Fin n,
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K i₀⟩ ↔
        ∃ g : G, inS g ∧ line (χ g) (K i) := by
    intro i
    constructor
    · intro hiso
      obtain ⟨c, d, hcd, hdc, htw, hline⟩ := exists_of_iso hΛo k E P ℓ L₀ (K i) (K i₀) hK₀' hiso
      obtain ⟨g, y, hy⟩ := hρ.label_surjective c d hcd hdc
      refine ⟨g, (hS_tw g).mpr (isTwist_of_sub_mem k E P (χ g) c ⟨y, hy⟩ htw), fun Q => ?_⟩
      rw [hline Q, pushPt_act_Q0_eq_of_sub_mem k E P ℓ (χ g) c ⟨y, hy⟩]
    · rintro ⟨g, hg, hline⟩
      exact iso_of_line hΛo k E P ℓ hℓk L₀ (K i) (K i₀) hK₀' (χ g) hline ((hS_tw g).mp hg)

  have hexists : ∀ g : G, inS g → ∃ i : Fin n, line (χ g) (K i) := fun g hg =>
    exists_index_line hΛo k E P ℓ L₀ n K hKexh i₀ hK₀' (χ g) (χ g⁻¹)
      (chi_mul_chi_inv χ hρ.label_one hρ.label_mul g) ((hS_tw g⁻¹).mp (hS_inv g hg))

  have huniq : ∀ (g g' : G) (i i' : Fin n), line (χ g) (K i) → line (χ g') (K i') →
      (i = i' ↔ g' * g⁻¹ ∈ H) := by
    intro g g' i i' hi hi'
    constructor
    · rintro rfl
      refine mem_of_forall_exists hΛo hm0 k E P ℓ hℓ0 hℓm L₀ hL₀ hℓL₀ χ hρ.label_one hρ.label_mul H hH g' g ?_
      intro x hx
      obtain ⟨x', hx', h'⟩ := (hi _).mp ((hi' _).mpr ⟨x, hx, rfl⟩)
      exact ⟨x', hx', h'⟩
    · intro hH'
      apply hKdist i i'
      intro x
      let Q : SchemeHomOver (geomPoint k (RingHom.id k)) E.f := ⟨x.1, by rw [geomPoint_id]; exact x.2⟩
      rw [factorsThrough_iff_of_val_eq (K i).levK x Q rfl, factorsThrough_iff_of_val_eq (K i').levK x Q rfl, hi Q, hi' Q]
      have hH'' : g * g'⁻¹ ∈ H := by
        have := H.inv_mem hH'; rwa [mul_inv_rev, inv_inv] at this
      constructor
      · rintro ⟨x₀, hx₀, hQ⟩
        obtain ⟨x', hx', h'⟩ := exists_line_of_mem hΛo hm0 k E P ℓ hℓ0 hℓm L₀ hL₀ hℓL₀ χ hρ.label_mul H hH g g' hH'' x₀ hx₀
        exact ⟨x', hx', h'.trans hQ⟩
      · rintro ⟨x₀, hx₀, hQ⟩
        obtain ⟨x', hx', h'⟩ := exists_line_of_mem hΛo hm0 k E P ℓ hℓ0 hℓm L₀ hL₀ hℓL₀ χ hρ.label_mul H hH g' g hH' x₀ hx₀
        exact ⟨x', hx', h'.trans hQ⟩

  have hΦex : ∀ g : {g : G // inS g}, ∃ i : Fin n, line (χ g.1) (K i) := fun g => hexists g.1 g.2
  choose Φ hΦ using hΦex
  have hrangeΦ : ∀ i : Fin n, (∃ g, Φ g = i) ↔
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K i₀⟩ := by
    intro i
    rw [hrange i]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, hΦ g⟩
    · rintro ⟨g, hg, hline⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      exact ((huniq g g (Φ ⟨g, hg⟩) i (hΦ ⟨g, hg⟩) hline).mpr (by rw [mul_inv_cancel]; exact H.one_mem))
  have hfibre : ∀ g g' : {g : G // inS g}, Φ g = Φ g' ↔ g'.1 * g.1⁻¹ ∈ H :=
    fun g g' => huniq g.1 g'.1 (Φ g) (Φ g') (hΦ g) (hΦ g')
  let T := {i : Fin n // FakeEllipticCurve.WithExtraLevel.Iso
    (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨E, K i₀⟩}
  let SH := {g : G // g ∈ H ∧ inS g}
  let Φ' : {g : G // inS g} → T := fun g => ⟨Φ g, (hrangeΦ (Φ g)).mp ⟨g, rfl⟩⟩
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨i, hi⟩
    obtain ⟨g, hg⟩ := (hrangeΦ i).mpr hi
    exact ⟨g, Subtype.ext hg⟩
  have hfib : ∀ t : T, Nat.card {g : {g : G // inS g} // Φ' g = t} = Nat.card SH := by
    intro t
    obtain ⟨g₀, hg₀⟩ := hΦ'surj t
    refine Nat.card_congr ?_
    refine Equiv.ofBijective (fun g => ⟨g.1.1 * g₀.1⁻¹, ?_, ?_⟩) ⟨?_, ?_⟩
    · exact (hfibre g₀ g.1).mp (by
        have h1 := congrArg Subtype.val g.2
        have h2 := congrArg Subtype.val hg₀
        exact h2.trans h1.symm)
    · exact hS_mul _ _ g.1.2 (hS_inv _ g₀.2)
    · rintro ⟨⟨g, hg⟩, hgt⟩ ⟨⟨g', hg'⟩, hg't⟩ h
      have h' : g * (g₀.1)⁻¹ = g' * (g₀.1)⁻¹ := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext
      exact mul_right_cancel h'
    · rintro ⟨h, hhH, hhS⟩
      refine ⟨⟨⟨h * g₀.1, hS_mul _ _ hhS g₀.2⟩, ?_⟩, ?_⟩
      · apply Subtype.ext
        show Φ ⟨h * g₀.1, _⟩ = t.1
        rw [← hg₀]
        show Φ ⟨h * g₀.1, _⟩ = Φ g₀
        exact ((hfibre ⟨h * g₀.1, hS_mul _ _ hhS g₀.2⟩ g₀).mpr (by
          show g₀.1 * (h * g₀.1)⁻¹ ∈ H
          rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
          exact H.inv_mem hhH))
      · apply Subtype.ext
        show h * g₀.1 * (g₀.1)⁻¹ = h
        exact mul_inv_cancel_right h g₀.1
  have key : Nat.card {g : G // inS g} = Nat.card T * Nat.card SH := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv Φ').symm, Nat.card_sigma]
    simp_rw [hfib]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  show Nat.card T * Nat.card SH = Nat.card {g : G // inS g}
  exact key.symm

#print axioms solution

end S_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq (solution)
