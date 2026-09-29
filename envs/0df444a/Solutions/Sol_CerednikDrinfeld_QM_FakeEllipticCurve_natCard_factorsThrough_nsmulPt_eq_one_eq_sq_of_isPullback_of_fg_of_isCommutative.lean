-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2f89eba6-393c-557f-a3c3-738f26e470ef

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
import Theorems.Thm_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective
import Theorems.Thm_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

noncomputable section

namespace CountBody

section A

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
variable {S' : Type} [CommRing S'] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')

theorem map_one_of_map_mul {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {T' : Scheme.{0}} {t' : T' ⟶ Spec (CommRingCat.of S')}
    (φ : SchemeHomOver t f → SchemeHomOver t' f')
    (hmul : ∀ x y, φ (L.mul t x y) = L'.mul t' (φ x) (φ y)) : φ (L.one t) = L'.one t' := by
  letI := L'.pointGroup t'
  have h := hmul (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h' : φ (L.one t) * φ (L.one t) = 1 * φ (L.one t) := h.symm.trans (one_mul _).symm
  exact mul_right_cancel h'

theorem map_nsmulPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {T' : Scheme.{0}} {t' : T' ⟶ Spec (CommRingCat.of S')}
    (φ : SchemeHomOver t f → SchemeHomOver t' f')
    (hmul : ∀ x y, φ (L.mul t x y) = L'.mul t' (φ x) (φ y)) (n : ℕ) (x : SchemeHomOver t f) :
    φ (nsmulPt L t n x) = nsmulPt L' t' n (φ x) := by
  induction n with
  | zero => exact map_one_of_map_mul L L' φ hmul
  | succ n ih =>
    show φ (L.mul t (nsmulPt L t n x) x) = L'.mul t' (nsmulPt L' t' n (φ x)) (φ x)
    rw [hmul, ih]

theorem natCard_congr_of_mul {C : Scheme.{0}} (lev : C ⟶ A) {C' : Scheme.{0}} (lev' : C' ⟶ A')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {T' : Scheme.{0}} {t' : T' ⟶ Spec (CommRingCat.of S')}
    (φ : SchemeHomOver t f ≃ SchemeHomOver t' f')
    (hmul : ∀ x y, φ (L.mul t x y) = L'.mul t' (φ x) (φ y))
    (hlev : ∀ x, FactorsThrough lev x ↔ FactorsThrough lev' (φ x)) (d : ℕ) :
    Nat.card {P : SchemeHomOver t f // FactorsThrough lev P ∧ nsmulPt L t d P = L.one t} =
      Nat.card {P : SchemeHomOver t' f' // FactorsThrough lev' P ∧ nsmulPt L' t' d P = L'.one t'} := by
  apply Nat.card_congr
  refine φ.subtypeEquiv ?_
  intro P
  rw [hlev, ← map_one_of_map_mul L L' φ hmul, ← map_nsmulPt L L' φ hmul, φ.injective.eq_iff]

theorem natCard_congr_base {C : Scheme.{0}} (lev : C ⟶ A) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)}
    (h : t₁ = t₂) (d : ℕ) :
    Nat.card {P : SchemeHomOver t₁ f // FactorsThrough lev P ∧ nsmulPt L t₁ d P = L.one t₁} =
      Nat.card {P : SchemeHomOver t₂ f // FactorsThrough lev P ∧ nsmulPt L t₂ d P = L.one t₂} := by
  subst h; rfl

end A

section B

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
  {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
  (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → nsmulPt L t N P = L.one t)
  (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
  (hN : IsUnit ((N : ℕ) : S)) (d : ℕ) (hd : d ∣ N)

abbrev kerι : L.schemeKer d ⟶ A := pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1

abbrev qY : pullback lev (kerι L d) ⟶ Spec (CommRingCat.of S) := pullback.fst lev (kerι L d) ≫ lev ≫ f

include hcomm hbundle hlev_closed hlev_torsion hlev_flat hlev_fp hN hd in
theorem finrank_qY_eq_natCard (k : Type) [Field k] [IsAlgClosed k] (τ : S →+* k) :
    (qY L lev d).finrank (Spec.map (CommRingCat.ofHom τ) (IsLocalRing.closedPoint k)) =
      Nat.card {P : SchemeHomOver (geomPoint k τ) f // FactorsThrough lev P ∧ nsmulPt L (geomPoint k τ) d P = L.one _} := by
  obtain ⟨hfin, het, hopen, hpts⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
      L hcomm hbundle lev hlev_closed N hlev_torsion hlev_flat hlev_fp hN d hd
  haveI := hfin; haveI := het; haveI := hopen; haveI := hlev_closed
  rw [AlgebraicGeometry.finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed (qY L lev d) k τ]

  haveI : Mono (pullback.fst lev (kerι L d) ≫ lev) := mono_comp _ _
  let toP : {w : Spec (CommRingCat.of k) ⟶ pullback lev (kerι L d) // w ≫ qY L lev d = Spec.map (CommRingCat.ofHom τ)} →
      {P : SchemeHomOver (geomPoint k τ) f // FactorsThrough lev P ∧ nsmulPt L (geomPoint k τ) d P = L.one _} :=
    fun w => ⟨⟨w.1 ≫ pullback.fst lev (kerι L d) ≫ lev, by
        show (w.1 ≫ pullback.fst lev (kerι L d) ≫ lev) ≫ f = Spec.map (CommRingCat.ofHom τ)
        simp only [Category.assoc]; exact w.2⟩,
      (hpts (geomPoint k τ) _).mp ⟨w.1, rfl⟩⟩
  apply Nat.card_congr
  refine Equiv.ofBijective toP ⟨?_, ?_⟩
  · intro w₁ w₂ h
    apply Subtype.ext
    have h1 : w₁.1 ≫ pullback.fst lev (kerι L d) ≫ lev = w₂.1 ≫ pullback.fst lev (kerι L d) ≫ lev :=
      congrArg (fun P => P.1.1) h
    exact (cancel_mono (pullback.fst lev (kerι L d) ≫ lev)).mp h1
  · rintro ⟨P, hP⟩
    obtain ⟨w, hw⟩ := (hpts (geomPoint k τ) P).mpr hP
    refine ⟨⟨w, ?_⟩, ?_⟩
    · show w ≫ pullback.fst lev (kerι L d) ≫ lev ≫ f = geomPoint k τ
      rw [reassoc_of% hw]; exact P.2
    · apply Subtype.ext; apply Subtype.ext
      exact hw

end B

section C

variable {R : Type} [CommRing R] {R' : Type} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {C : Scheme.{0}} (lev : C ⟶ A)

abbrev levBC : pullback lev (pullback.fst f ι) ⟶ RelativeGroupLaw.baseChangeScheme ι f := pullback.snd lev (pullback.fst f ι)

theorem factorsThrough_levBC_iff {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P' : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    FactorsThrough (levBC ι lev) P' ↔ FactorsThrough lev (RelativeGroupLaw.baseChangePointToBase ι P') := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst lev (pullback.fst f ι), ?_⟩
    rw [RelativeGroupLaw.baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, pullback.condition]
  · rintro ⟨Q₀, hQ₀⟩
    rw [RelativeGroupLaw.baseChangePointToBase_coe] at hQ₀
    exact ⟨pullback.lift Q₀ P'.1 hQ₀, pullback.lift_snd _ _ _⟩

theorem natCard_baseChange {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (d : ℕ) :
    Nat.card {P' : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f) //
        FactorsThrough (levBC ι lev) P' ∧ nsmulPt (L.baseChange ι) t' d P' = (L.baseChange ι).one t'} =
      Nat.card {P : SchemeHomOver (t' ≫ ι) f // FactorsThrough lev P ∧ nsmulPt L (t' ≫ ι) d P = L.one _} :=
  natCard_congr_of_mul (L.baseChange ι) L (levBC ι lev) lev (RelativeGroupLaw.baseChangePointEquiv ι t')
    (fun x y => RelativeGroupLaw.baseChangePointToBase_mul ι L t' x y)
    (fun x => factorsThrough_levBC_iff ι lev x) d

theorem levBC_torsion (N : ℕ)
    (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P' : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f))
    (h : FactorsThrough (levBC ι lev) P') : nsmulPt (L.baseChange ι) t' N P' = (L.baseChange ι).one t' := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι t').injective
  show RelativeGroupLaw.baseChangePointToBase ι (nsmulPt (L.baseChange ι) t' N P') =
    RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).one t')
  rw [map_nsmulPt (L.baseChange ι) L (RelativeGroupLaw.baseChangePointToBase ι)
      (fun x y => RelativeGroupLaw.baseChangePointToBase_mul ι L t' x y),
    RelativeGroupLaw.baseChangePointToBase_one]
  exact hlev_torsion _ _ ((factorsThrough_levBC_iff ι lev P').mp h)

theorem isPullback_levBC :
    IsPullback (pullback.fst lev (pullback.fst f ι)) (levBC ι lev ≫ RelativeGroupLaw.baseChangeStr ι f) (lev ≫ f) ι :=
  IsPullback.paste_vert (IsPullback.of_hasPullback lev (pullback.fst f ι)) (IsPullback.of_hasPullback f ι)

end C

section D

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {L : Type} [CommRing L] (E : FakeEllipticCurve Λ N L)
  (R : Subalgebra ℤ L) {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)} (L₀ : RelativeGroupLaw ↥R f₀)
  {C₀ : Scheme.{0}} (lev₀ : C₀ ⟶ A₀)
  (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
  (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
    (E.L.mul t' P Q).1 ≫ g =
      (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
  (gC : E.C ⟶ C₀) (hgC : CategoryTheory.IsPullback gC E.lev lev₀ g)

def pushG {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (Q : SchemeHomOver t' E.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom)) f₀ :=
  ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩

def pushGEquiv {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) :
    SchemeHomOver t' E.f ≃ SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom)) f₀ where
  toFun := pushG E R g hg t'
  invFun P := ⟨hg.lift P.1 t' P.2, hg.lift_snd _ _ _⟩
  left_inv Q := by
    apply Subtype.ext
    apply hg.hom_ext
    · rw [hg.lift_fst]; rfl
    · rw [hg.lift_snd]; exact Q.2.symm
  right_inv P := by
    apply Subtype.ext
    show hg.lift P.1 t' P.2 ≫ g = P.1
    exact hg.lift_fst _ _ _

include hmul in
theorem pushG_mul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f) :
    pushGEquiv E R g hg t' (E.L.mul t' P Q) =
      L₀.mul _ (pushGEquiv E R g hg t' P) (pushGEquiv E R g hg t' Q) :=
  Subtype.ext (hmul t' P Q)

include hgC in
theorem factorsThrough_pushG_iff {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (Q : SchemeHomOver t' E.f) :
    FactorsThrough E.lev Q ↔ FactorsThrough lev₀ (pushGEquiv E R g hg t' Q) := by
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    refine ⟨Q₀ ≫ gC, ?_⟩
    show (Q₀ ≫ gC) ≫ lev₀ = Q.1 ≫ g
    rw [Category.assoc, hgC.w, ← Category.assoc, hQ₀]
  · rintro ⟨P₀, hP₀⟩
    change P₀ ≫ lev₀ = Q.1 ≫ g at hP₀
    exact ⟨hgC.lift P₀ Q.1 hP₀, hgC.lift_snd _ _ _⟩

include hmul hgC in
theorem natCard_pushG {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (d : ℕ) :
    Nat.card {Q : SchemeHomOver t' E.f // FactorsThrough E.lev Q ∧ nsmulPt E.L t' d Q = E.L.one t'} =
      Nat.card {P : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom)) f₀ //
        FactorsThrough lev₀ P ∧ nsmulPt L₀ _ d P = L₀.one _} :=
  natCard_congr_of_mul E.L L₀ E.lev lev₀ (pushGEquiv E R g hg t') (fun x y => pushG_mul E R L₀ g hg hmul t' x y)
    (fun x => factorsThrough_pushG_iff E R lev₀ g hg gC hgC t' x) d

end D

section Epts

theorem geomPoint_comp {S S' : Type} [CommRing S] [CommRing S'] (k : Type) [Field k] (σ : S' →+* k) (φ : S →+* S') :
    geomPoint k (σ.comp φ) = geomPoint k σ ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold geomPoint
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end Epts

end CountBody

open CountBody in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L)
    (R : Subalgebra ℤ L) (hR : R.FG)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
    (hcomm₀ : L₀.IsCommutative) (hbundle₀ : AbelianSchemePropertyBundle ↥R f₀)
    (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (hlev_closed₀ : IsClosedImmersion lev₀)
    (hlev_sub₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
    (hlev_one₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
    (hlev_torsion₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
    (hlev_finite₀ : IsFinite (lev₀ ≫ f₀)) (hlev_flat₀ : Flat (lev₀ ≫ f₀)) (hlev_fp₀ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
    (hlev_rank₀ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), (lev₀ ≫ f₀).finrank s = N ^ 2)
    (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (gC : E.C ⟶ C₀) (hgC : CategoryTheory.IsPullback gC E.lev lev₀ g) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R →+* k), (N : k) ≠ 0 →
      ∀ d : ℕ, d ∣ N →
        Nat.card {P : SchemeHomOver (geomPoint k sk) f₀ //
          FactorsThrough lev₀ P ∧ nsmulPt L₀ (geomPoint k sk) d P = L₀.one (geomPoint k sk)} = d ^ 2 := by
  intro k _ _ sk hNk d hd
  classical

  let M : Submonoid ↥R := Submonoid.powers ((N : ℕ) : ↥R)
  let R' : Type := Localization.Away ((N : ℕ) : ↥R)
  let L' : Type := Localization (M.map R.val.toRingHom)
  have hskN : IsUnit (sk ((N : ℕ) : ↥R)) := by rw [map_natCast]; exact isUnit_iff_ne_zero.mpr hNk
  let sk' : R' →+* k := IsLocalization.Away.lift ((N : ℕ) : ↥R) hskN
  have hsk' : sk'.comp (algebraMap ↥R R') = sk := IsLocalization.Away.lift_comp _ hskN
  let φ : R' →+* L' := IsLocalization.map L' R.val.toRingHom M.le_comap_map
  have hφinj : Function.Injective φ :=
    IsLocalization.map_injective_of_injective M R' L' (fun x y h => Subtype.ext h)
  have hφcomp : φ.comp (algebraMap ↥R R') = (algebraMap L L').comp R.val.toRingHom := IsLocalization.map_comp _
  let ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of ↥R) := Spec.map (CommRingCat.ofHom (algebraMap ↥R R'))
  have hNR' : IsUnit ((N : ℕ) : R') := by
    have := IsLocalization.Away.algebraMap_isUnit (S := R') ((N : ℕ) : ↥R)
    rwa [map_natCast] at this
  have hNL' : IsUnit ((N : ℕ) : L') := by
    have := hNR'.map φ
    rwa [map_natCast] at this

  let G' := L₀.baseChange ι
  have hcomm' : G'.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange ι hcomm₀
  have hbundle' : AbelianSchemePropertyBundle R' (RelativeGroupLaw.baseChangeStr ι f₀) :=
    hbundle₀.of_isPullback (IsPullback.of_hasPullback f₀ ι)
  have hlev_closed' : IsClosedImmersion (levBC (f := f₀) ι lev₀) := by haveI := hlev_closed₀; infer_instance
  have hsq := isPullback_levBC (f := f₀) ι lev₀
  have hlev_flat' : Flat (levBC (f := f₀) ι lev₀ ≫ RelativeGroupLaw.baseChangeStr ι f₀) :=
    MorphismProperty.of_isPullback hsq hlev_flat₀
  have hlev_fp' : LocallyOfFinitePresentation (levBC (f := f₀) ι lev₀ ≫ RelativeGroupLaw.baseChangeStr ι f₀) :=
    MorphismProperty.of_isPullback hsq hlev_fp₀
  have hlev_torsion' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R'))
      (P' : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f₀)),
      FactorsThrough (levBC (f := f₀) ι lev₀) P' → nsmulPt G' t' N P' = G'.one t' :=
    fun t' P' h => levBC_torsion ι L₀ lev₀ N hlev_torsion₀ t' P' h

  have hpt : geomPoint k sk = geomPoint k sk' ≫ ι := by
    rw [← hsk']; exact geomPoint_comp k sk' (algebraMap ↥R R')
  rw [natCard_congr_base L₀ lev₀ hpt d, ← natCard_baseChange ι L₀ lev₀ (geomPoint k sk') d,
    ← finrank_qY_eq_natCard G' hcomm' hbundle' (levBC (f := f₀) ι lev₀) hlev_closed' N hlev_torsion' hlev_flat' hlev_fp' hNR'
      d hd k sk']

  obtain ⟨hfin, het, -, -⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
      G' hcomm' hbundle' (levBC (f := f₀) ι lev₀) hlev_closed' N hlev_torsion' hlev_flat' hlev_fp' hNR' d hd
  haveI := hfin
  haveI := het
  have hsmY : Smooth (qY G' (levBC (f := f₀) ι lev₀) d) := inferInstance
  have hflY : Flat (qY G' (levBC (f := f₀) ι lev₀) d) := inferInstance
  have hfpY : LocallyOfFinitePresentation (qY G' (levBC (f := f₀) ι lev₀) d) := inferInstance
  refine AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective φ hφinj (qY G' (levBC (f := f₀) ι lev₀) d) hfin
    hflY hfpY
    (pullback.snd (qY G' (levBC (f := f₀) ι lev₀) d) (Spec.map (CommRingCat.ofHom φ)))
    (pullback.fst (qY G' (levBC (f := f₀) ι lev₀) d) (Spec.map (CommRingCat.ofHom φ)))
    (IsPullback.of_hasPullback _ _) (d ^ 2) (fun x => ?_) _

  let X := Spec (CommRingCat.of L')
  let kx : Type := AlgebraicClosure (X.residueField x)
  let gx : Spec (CommRingCat.of kx) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) kx)) ≫ X.fromSpecResidueField x
  let σ'' : L' →+* kx := (Spec.preimage gx).hom
  have hσ : Spec.map (CommRingCat.ofHom σ'') = gx := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage gx).hom) = gx
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hx : Spec.map (CommRingCat.ofHom σ'') (IsLocalRing.closedPoint kx) = x := by
    rw [hσ]
    show (Spec.map _ ≫ X.fromSpecResidueField x) _ = x
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  rw [Scheme.Hom.finrank_pullback_snd, ← hx, ← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hNkx : ((N : ℕ) : kx) ≠ 0 := by
    have := hNL'.map σ''
    rw [map_natCast] at this
    exact this.ne_zero
  rw [finrank_qY_eq_natCard G' hcomm' hbundle' (levBC (f := f₀) ι lev₀) hlev_closed' N hlev_torsion' hlev_flat' hlev_fp' hNR'
      d hd kx (σ''.comp φ), natCard_baseChange ι L₀ lev₀ (geomPoint kx (σ''.comp φ)) d]
  have hpt2 : geomPoint kx (σ''.comp φ) ≫ ι =
      geomPoint kx (σ''.comp (algebraMap L L')) ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom) := by
    rw [← geomPoint_comp, ← geomPoint_comp, RingHom.comp_assoc, hφcomp, ← RingHom.comp_assoc]
  rw [natCard_congr_base L₀ lev₀ hpt2 d, ← natCard_pushG E R L₀ lev₀ g hg hmul gC hgC (geomPoint kx (σ''.comp (algebraMap L L'))) d]
  exact CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_lev_nsmulPt_eq_one_eq_sq E kx
    (σ''.comp (algebraMap L L')) hNkx d hd

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative (solution)
