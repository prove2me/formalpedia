-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7846178d-8ac2-563a-8dd3-bcb2fd105321

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open CategoryTheory.Limits

namespace L2bAsm
open CerednikDrinfeld.QM

section grp
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : GoodReductionJacobian.RelativeGroupLaw R f)

theorem mul_inv_cancel {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  have h1 : G.mul t (G.inv t (G.inv t x)) (G.inv t x) = G.one t := G.inv_mul_cancel t _
  have h2 : G.mul t (G.inv t x) (G.mul t x (G.inv t x)) = G.inv t x := by
    rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul]
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by rw [h1]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [h2]
    _ = G.one t := h1

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f)
    (h : G.mul t y x = G.one t) : y = G.inv t x := by
  calc y = G.mul t y (G.one t) := (G.mul_one t y).symm
    _ = G.mul t y (G.mul t x (G.inv t x)) := by rw [mul_inv_cancel]
    _ = G.mul t (G.mul t y x) (G.inv t x) := (G.mul_assoc t _ _ _).symm
    _ = G.inv t x := by rw [h, G.one_mul]

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

variable {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
  (m : T' ⟶ T) (hm : m ≫ t = t')

noncomputable abbrev res (P : SchemeHomOver t f) : SchemeHomOver t' f := GoodReductionJacobian.schemeHomOverComp m hm P

theorem res_coe (P : SchemeHomOver t f) : (res t t' m hm P).1 = m ≫ P.1 := rfl

theorem res_mul (P Q : SchemeHomOver t f) : res t t' m hm (G.mul t P Q) = G.mul t' (res t t' m hm P) (res t t' m hm Q) :=
  G.mul_natural t t' m hm P Q

theorem res_one : res t t' m hm (G.one t) = G.one t' := by
  apply eq_one_of_mul_self
  rw [← res_mul, G.one_mul]

theorem res_inv (P : SchemeHomOver t f) : res t t' m hm (G.inv t P) = G.inv t' (res t t' m hm P) := by
  apply eq_inv_of_mul_eq_one
  rw [← res_mul, G.inv_mul_cancel, res_one]

theorem res_nsmul (n : ℕ) (P : SchemeHomOver t f) :
    res t t' m hm (nsmulPt G t n P) = nsmulPt G t' n (res t t' m hm P) := by
  induction n with
  | zero => exact res_one G t t' m hm
  | succ n ih =>
    show res t t' m hm (G.mul t (nsmulPt G t n P) P) = G.mul t' (nsmulPt G t' n (res t t' m hm P)) (res t t' m hm P)
    rw [res_mul, ih]

omit G in
theorem res_pushPt (φ' : A ⟶ A) (hφ' : φ' ≫ f = f) (P : SchemeHomOver t f) :
    res t t' m hm (pushPt φ' hφ' P) = pushPt φ' hφ' (res t t' m hm P) := by
  apply Subtype.ext
  simp only [res_coe, mapPt_coe, Category.assoc]

omit G in
theorem factorsThrough_res {C : Scheme.{u}} (lev : C ⟶ A) (P : SchemeHomOver t f) (h : FactorsThrough lev P) :
    FactorsThrough lev (res t t' m hm P) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨m ≫ Q, by rw [Category.assoc, hQ]; rfl⟩

def castPt {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    SchemeHomOver t₁ f ≃ SchemeHomOver t₂ f :=
  Equiv.subtypeEquivRight (fun _ => by rw [h])

omit G in
@[scoped simp] theorem castPt_coe {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P : SchemeHomOver t₁ f) : (castPt (f := f) h P).1 = P.1 := rfl

theorem mul_castPt {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) :
    G.mul t₂ (castPt (f := f) h P) (castPt (f := f) h Q) = castPt (f := f) h (G.mul t₁ P Q) := by
  subst h
  rfl

end grp

end L2bAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover.L2bAsm"

open L2bAsm in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (n : ℕ)
    {ι : Type u} (Sᵢ : ι → Type u) [∀ i, CommRing (Sᵢ i)] (φ : ∀ i, S →+* Sᵢ i)
    (hopen : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ i))))
    (hcover : ∀ x : ↥(Spec (CommRingCat.of S)), ∃ i, x ∈ Set.range (Spec.map (CommRingCat.ofHom (φ i))).base)
    (Eᵢ : ∀ i, FakeEllipticCurve Λ N (Sᵢ i))
    (g : ∀ i, (Eᵢ i).A ⟶ E.A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (Eᵢ i).f E.f (Spec.map (CommRingCat.ofHom (φ i))))
    (hg_mul : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P Q : SchemeHomOver t (Eᵢ i).f),
      ((Eᵢ i).L.mul t P Q).1 ≫ g i =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ (i : ι) (x : ↥Λ), (Eᵢ i).act x ≫ g i = g i ≫ E.act x)
    (hg_lev : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
      FactorsThrough E.lev (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ →
        FactorsThrough (Eᵢ i).lev P)
    (K : ∀ i, (Eᵢ i).ExtraLevel n)
    (hK : ∀ (i j : ι) {T : Scheme.{u}}
      (tᵢ : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (tⱼ : T ⟶ Spec (CommRingCat.of (Sᵢ j)))
      (Pᵢ : SchemeHomOver tᵢ (Eᵢ i).f) (Pⱼ : SchemeHomOver tⱼ (Eᵢ j).f),
      Pᵢ.1 ≫ g i = Pⱼ.1 ≫ g j → (FactorsThrough (K i).levK Pᵢ ↔ FactorsThrough (K j).levK Pⱼ)) :
    ∃ K₀ : E.ExtraLevel n,
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
        FactorsThrough K₀.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
            ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
          FactorsThrough (K i).levK P) ∧
      (∀ K₁ : E.ExtraLevel n,
        (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
          FactorsThrough K₁.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
              ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
            FactorsThrough (K i).levK P) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K₁.levK P ↔ FactorsThrough K₀.levK P) := by
  classical

  haveI hgo : ∀ i, IsOpenImmersion (g i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hg i).flip (hopen i)
  haveI hgq : ∀ i, QuasiCompact (g i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hg i).flip inferInstance
  haveI hzc : ∀ i, IsClosedImmersion ((K i).levK) := fun i => (K i).levK_closed

  have hcoverA : ∀ x : ↥E.A, ∃ i, x ∈ Set.range (g i).base := by
    intro x
    obtain ⟨i, hi⟩ := hcover (E.f.base x)
    have hx : x ∈ Set.range (pullback.fst E.f (Spec.map (CommRingCat.ofHom (φ i)))).base := by
      rw [Scheme.Pullback.range_fst]; exact hi
    obtain ⟨z, rfl⟩ := hx
    refine ⟨i, (hg i).isoPullback.inv.base z, ?_⟩
    change ((hg i).isoPullback.inv ≫ g i).base z = _
    rw [IsPullback.isoPullback_inv_fst]
  have hagree : ∀ (i j : ι) {T : Scheme.{u}} (Pᵢ : T ⟶ (Eᵢ i).A) (Pⱼ : T ⟶ (Eᵢ j).A),
      Pᵢ ≫ g i = Pⱼ ≫ g j →
        ((∃ Q : T ⟶ (K i).K, Q ≫ (K i).levK = Pᵢ) ↔ (∃ Q : T ⟶ (K j).K, Q ≫ (K j).levK = Pⱼ)) := by
    intro i j T Pᵢ Pⱼ h
    exact hK i j (Pᵢ ≫ (Eᵢ i).f) (Pⱼ ≫ (Eᵢ j).f) ⟨Pᵢ, rfl⟩ ⟨Pⱼ, rfl⟩ h
  obtain ⟨K0, k0, hk0, hcart, hloc, huniq⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
      (fun i => (Eᵢ i).A) g hcoverA (fun i => (K i).K) (fun i => (K i).levK) hagree
  choose zK hzK using hcart

  have hA : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
      FactorsThrough k0 (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
        FactorsThrough (K i).levK P := by
    intro i T t P
    constructor
    · rintro ⟨Q, hQ⟩
      exact ⟨(hzK i).lift P.1 Q hQ.symm, (hzK i).lift_fst _ _ _⟩
    · rintro ⟨Q, hQ⟩
      exact ⟨Q ≫ zK i, by rw [Category.assoc, ← (hzK i).w, ← Category.assoc, hQ]⟩

  have hbig : ∀ i, IsPullback (zK i) ((K i).levK ≫ (Eᵢ i).f) (k0 ≫ E.f) (Spec.map (CommRingCat.ofHom (φ i))) :=
    fun i => (hzK i).flip.paste_vert (hg i)

  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover :=
    Scheme.Cover.mkOfCovers ι (fun i => Spec (CommRingCat.of (Sᵢ i))) (fun i => Spec.map (CommRingCat.ofHom (φ i)))
      (fun x => by obtain ⟨i, y, hy⟩ := hcover x; exact ⟨i, y, hy⟩) hopen
  have hfin : IsFinite (k0 ≫ E.f) := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i => ?_)
    haveI := (K i).levK_finite
    change IsFinite (pullback.snd (k0 ≫ E.f) (Spec.map (CommRingCat.ofHom (φ i))))
    rw [← (hbig i).isoPullback_inv_snd]
    infer_instance
  have hflat : Flat (k0 ≫ E.f) := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i => ?_)
    haveI := (K i).levK_flat
    change Flat (pullback.snd (k0 ≫ E.f) (Spec.map (CommRingCat.ofHom (φ i))))
    rw [← (hbig i).isoPullback_inv_snd]
    infer_instance
  have hlfp : LocallyOfFinitePresentation (k0 ≫ E.f) := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i => ?_)
    haveI := (K i).levK_finitePresentation
    change LocallyOfFinitePresentation (pullback.snd (k0 ≫ E.f) (Spec.map (CommRingCat.ofHom (φ i))))
    rw [← (hbig i).isoPullback_inv_snd]
    infer_instance

  have hchart : ∀ (i : ι) {T' : Scheme.{u}} (tV : T' ⟶ Spec (CommRingCat.of (Sᵢ i))),
      ∃ σ : SchemeHomOver tV (Eᵢ i).f ≃ SchemeHomOver (tV ≫ Spec.map (CommRingCat.ofHom (φ i))) E.f,
        (∀ P, (σ P).1 = P.1 ≫ g i) ∧
        σ ((Eᵢ i).L.one tV) = E.L.one _ ∧
        (∀ P Q, σ ((Eᵢ i).L.mul tV P Q) = E.L.mul _ (σ P) (σ Q)) ∧
        (∀ P, σ ((Eᵢ i).L.inv tV P) = E.L.inv _ (σ P)) ∧
        (∀ (n : ℕ) P, σ (nsmulPt (Eᵢ i).L tV n P) = nsmulPt E.L _ n (σ P)) ∧
        (∀ (x : ↥Λ) P, σ (pushPt ((Eᵢ i).act x) ((Eᵢ i).act_over x) P) = pushPt (E.act x) (E.act_over x) (σ P)) ∧
        (∀ P', FactorsThrough k0 P' ↔ FactorsThrough (K i).levK (σ.symm P')) := by
    intro i T' tV
    obtain ⟨σ, h1, h2, h3, h4, h5, h6⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback (φ i) E (Eᵢ i) (g i) (hg i)
        (hg_mul i) (hg_act i) tV
    refine ⟨σ, h1, h2, h3, h4, h5, h6, fun P' => ?_⟩
    have hP' : P'.1 = (σ.symm P').1 ≫ g i := by rw [← h1, Equiv.apply_symm_apply]
    constructor
    · rintro ⟨Q, hQ⟩
      exact (hA i tV (σ.symm P')).mp ⟨Q, hQ.trans hP'⟩
    · intro h
      obtain ⟨Q, hQ⟩ := (hA i tV (σ.symm P')).mpr h
      exact ⟨Q, hQ.trans hP'.symm⟩

  have hmk : ∀ (i : ι) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (R : SchemeHomOver t E.f)
      (m : T' ⟶ T) (PV : T' ⟶ (Eᵢ i).A), m ≫ R.1 = PV ≫ g i →
      m ≫ t = (PV ≫ (Eᵢ i).f) ≫ Spec.map (CommRingCat.ofHom (φ i)) := by
    intro i T T' t R m PV h
    rw [← R.2, ← Category.assoc, h, Category.assoc, (hg i).w, Category.assoc]

  have hfinish : ∀ (i : ι) {T' : Scheme.{u}} {tV : T' ⟶ Spec (CommRingCat.of (Sᵢ i))} (PV : T' ⟶ (Eᵢ i).A)
      (Rᵢ : SchemeHomOver tV (Eᵢ i).f), FactorsThrough (K i).levK Rᵢ → Rᵢ.1 ≫ g i = PV ≫ g i →
      ∃ Q : T' ⟶ (K i).K, Q ≫ (K i).levK = PV := by
    intro i T' tV PV Rᵢ hR h
    obtain ⟨Q, hQ⟩ := hR
    exact ⟨Q, hQ.trans ((cancel_mono (g i)).mp h)⟩
  refine ⟨{ K := K0, levK := k0, levK_closed := hk0,
            levK_sub := ?_, levK_one := ?_, levK_torsion := ?_, levK_stable := ?_, levK_disjoint := ?_,
            levK_finite := hfin, levK_flat := hflat, levK_finitePresentation := hlfp,
            levK_rank := ?_, levK_fibre := ?_ }, ?_, ?_⟩
  ·
    intro T t P Q hP hQ
    constructor
    · refine (hloc _).mpr ?_
      intro i V PV hPV
      have hm := hmk i t (E.L.mul t P Q) V.ι PV hPV
      obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (PV ≫ (Eᵢ i).f)
      have hPi := (h7 _).mp (L2bAsm.factorsThrough_res t _ V.ι hm k0 P hP)
      have hQi := (h7 _).mp (L2bAsm.factorsThrough_res t _ V.ι hm k0 Q hQ)
      refine hfinish i PV _ ((K i).levK_sub _ _ _ hPi hQi).1 ?_
      rw [← h1, h3, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← L2bAsm.res_mul E.L t _ V.ι hm]
      exact hPV
    · refine (hloc _).mpr ?_
      intro i V PV hPV
      have hm := hmk i t (E.L.inv t P) V.ι PV hPV
      obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (PV ≫ (Eᵢ i).f)
      have hPi := (h7 _).mp (L2bAsm.factorsThrough_res t _ V.ι hm k0 P hP)
      refine hfinish i PV _ ((K i).levK_sub _ _ _ hPi hPi).2 ?_
      rw [← h1, h4, Equiv.apply_symm_apply, ← L2bAsm.res_inv E.L t _ V.ι hm]
      exact hPV
  ·
    intro T t
    refine (hloc _).mpr ?_
    intro i V PV hPV
    have hm := hmk i t (E.L.one t) V.ι PV hPV
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (PV ≫ (Eᵢ i).f)
    refine hfinish i PV _ ((K i).levK_one (PV ≫ (Eᵢ i).f)) ?_
    rw [← h1, h2, ← L2bAsm.res_one E.L t _ V.ι hm]
    exact hPV
  ·
    intro T t P hP
    apply Subtype.ext
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ t) _ _ (fun i => ?_)
    have hm : pullback.fst t (Spec.map (CommRingCat.ofHom (φ i))) ≫ t =
        pullback.snd t (Spec.map (CommRingCat.ofHom (φ i))) ≫ Spec.map (CommRingCat.ofHom (φ i)) :=
      pullback.condition
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (pullback.snd t (Spec.map (CommRingCat.ofHom (φ i))))
    have hPi := (h7 _).mp (L2bAsm.factorsThrough_res t _ _ hm k0 P hP)
    have key := (K i).levK_torsion _ _ hPi
    apply_fun σ at key
    rw [h5, h2, Equiv.apply_symm_apply, ← L2bAsm.res_nsmul E.L t _ _ hm, ← L2bAsm.res_one E.L t _ _ hm] at key
    exact congrArg Subtype.val key
  ·
    intro x T t P hP
    refine (hloc _).mpr ?_
    intro i V PV hPV
    have hm := hmk i t (pushPt (E.act x) (E.act_over x) P) V.ι PV hPV
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (PV ≫ (Eᵢ i).f)
    have hPi := (h7 _).mp (L2bAsm.factorsThrough_res t _ V.ι hm k0 P hP)
    refine hfinish i PV _ ((K i).levK_stable x _ _ hPi) ?_
    rw [← h1, h6, Equiv.apply_symm_apply, ← L2bAsm.res_pushPt t _ V.ι hm]
    exact hPV
  ·
    intro T t P hP hlev
    apply Subtype.ext
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ t) _ _ (fun i => ?_)
    have hm : pullback.fst t (Spec.map (CommRingCat.ofHom (φ i))) ≫ t =
        pullback.snd t (Spec.map (CommRingCat.ofHom (φ i))) ≫ Spec.map (CommRingCat.ofHom (φ i)) :=
      pullback.condition
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (pullback.snd t (Spec.map (CommRingCat.ofHom (φ i))))
    have hPi := (h7 _).mp (L2bAsm.factorsThrough_res t _ _ hm k0 P hP)
    have hlev' : FactorsThrough (Eᵢ i).lev (σ.symm (L2bAsm.res t _ _ hm P)) := by
      apply hg_lev i
      obtain ⟨Q, hQ⟩ := L2bAsm.factorsThrough_res t _ _ hm E.lev P hlev
      refine ⟨Q, ?_⟩
      rw [hQ]
      change _ = (σ.symm _).1 ≫ g i
      rw [← h1, Equiv.apply_symm_apply]
    have key := (K i).levK_disjoint _ _ hPi hlev'
    apply_fun σ at key
    rw [h2, Equiv.apply_symm_apply, ← L2bAsm.res_one E.L t _ _ hm] at key
    exact congrArg Subtype.val key
  ·
    intro s
    obtain ⟨i, y, hy⟩ := hcover s
    haveI := hflat
    haveI := hfin
    rw [← hy, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (hbig i) y]
    exact (K i).levK_rank y
  ·
    intro k _ _ sk hnk

    obtain ⟨i, hi⟩ := hcover ((geomPoint k sk).base default)
    have H' : Set.range (geomPoint k sk).base ⊆ Set.range (Spec.map (CommRingCat.ofHom (φ i))).base := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z default]
      exact hi
    obtain ⟨φk, hφk⟩ := Spec.map_surjective (IsOpenImmersion.lift (Spec.map (CommRingCat.ofHom (φ i))) (geomPoint k sk) H')
    set skᵢ : Sᵢ i →+* k := φk.hom with hsk
    have hgeom : geomPoint k skᵢ = IsOpenImmersion.lift (Spec.map (CommRingCat.ofHom (φ i))) (geomPoint k sk) H' := by
      rw [← hφk]; rfl
    have heq : geomPoint k skᵢ ≫ Spec.map (CommRingCat.ofHom (φ i)) = geomPoint k sk := by
      rw [hgeom, IsOpenImmersion.lift_fac]
    obtain ⟨eᵢ, heᵢ⟩ := (K i).levK_fibre k skᵢ hnk
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := hchart i (geomPoint k skᵢ)
    let τ : SchemeHomOver (geomPoint k skᵢ) (Eᵢ i).f ≃ SchemeHomOver (geomPoint k sk) E.f :=
      σ.trans (L2bAsm.castPt (f := E.f) heq)
    have hτ : ∀ P, FactorsThrough (K i).levK P ↔ FactorsThrough k0 (τ P) := by
      intro P
      change FactorsThrough (K i).levK P ↔ FactorsThrough k0 (σ P)
      rw [h7, Equiv.symm_apply_apply]
    refine ⟨eᵢ.trans (τ.subtypeEquiv hτ), fun x y => ?_⟩
    simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
    change τ (eᵢ (x + y)).1 = E.L.mul (geomPoint k sk) (τ (eᵢ x).1) (τ (eᵢ y).1)
    rw [heᵢ]
    change L2bAsm.castPt (f := E.f) heq (σ _) =
      E.L.mul (geomPoint k sk) (L2bAsm.castPt (f := E.f) heq (σ _)) (L2bAsm.castPt (f := E.f) heq (σ _))
    rw [h3, L2bAsm.mul_castPt]
  ·
    intro i T t P
    exact hA i t P
  ·
    intro K₁ hK₁ T t P
    exact huniq K₁.K K₁.levK K₁.levK_closed (fun i {T'} (Q : T' ⟶ (Eᵢ i).A) => hK₁ i (Q ≫ (Eᵢ i).f) ⟨Q, rfl⟩) P.1

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover (solution)
