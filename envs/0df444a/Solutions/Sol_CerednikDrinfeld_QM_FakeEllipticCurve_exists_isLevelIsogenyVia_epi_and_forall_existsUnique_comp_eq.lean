-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2627d2a9-c41d-52fd-9aba-1d43b655c1cd

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

namespace P8IMGSUB

variable {R : Type u} [CommRing R]
  {A₀ A : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R)} {f : A ⟶ Spec (CommRingCat.of R)}
  (L₀ : RelativeGroupLaw R f₀) (L : RelativeGroupLaw R f)
  (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
  (hp_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
  {C₀ : Scheme.{u}} (ι : C₀ ⟶ A₀)
  (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (L₀.mul t P Q) ∧ FactorsThrough ι (L₀.inv t P))
  (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
    FactorsThrough ι P → mapPt p hp P = L.one t → P = L₀.one t)

include hp_hom in
theorem map_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt p hp (L₀.one t) = L.one t := by
  have h := hp_hom t (L₀.one t) (L₀.one t)
  rw [L₀.one_mul] at h
  have := congrArg (L.mul t (L.inv t (mapPt p hp (L₀.one t)))) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this.symm

include hp_hom in
theorem map_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀) :
    mapPt p hp (L₀.inv t P) = L.inv t (mapPt p hp P) := by
  letI := L.pointGroup t
  have h := hp_hom t (L₀.inv t P) P
  rw [L₀.inv_mul_cancel, map_one L₀ L p hp hp_hom] at h
  exact (inv_eq_of_mul_eq_one_left h.symm).symm

include hp_hom hsub hdisj in

theorem inj {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀)
    (hP : FactorsThrough ι P) (hQ : FactorsThrough ι Q) (h : mapPt p hp P = mapPt p hp Q) : P = Q := by
  letI := L₀.pointGroup t
  letI := L.pointGroup t
  have hD : FactorsThrough ι (L₀.mul t P (L₀.inv t Q)) := (hsub t _ _ hP (hsub t Q Q hQ hQ).2).1
  have hpD : mapPt p hp (L₀.mul t P (L₀.inv t Q)) = L.one t := by
    rw [hp_hom, map_inv L₀ L p hp hp_hom, h]; exact mul_inv_cancel (mapPt p hp Q)
  have := hdisj t _ hD hpD
  exact mul_inv_eq_one.1 this

include hp_hom hsub hdisj in

theorem isClosedImmersion [IsClosedImmersion ι] [IsFinite (ι ≫ p)] : IsClosedImmersion (ι ≫ p) := by
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  refine ⟨inferInstance, ⟨fun {T} c₁ c₂ hc => ?_⟩⟩

  have ht : c₂ ≫ ι ≫ f₀ = c₁ ≫ ι ≫ f₀ := by
    rw [← hp, ← Category.assoc ι, ← Category.assoc, ← hc, Category.assoc, Category.assoc]
  have h := inj L₀ L p hp hp_hom ι hsub hdisj (c₁ ≫ ι ≫ f₀) ⟨c₁ ≫ ι, by rw [Category.assoc]⟩ ⟨c₂ ≫ ι, by rw [Category.assoc, ht]⟩
    ⟨c₁, rfl⟩ ⟨c₂, rfl⟩ (by apply Subtype.ext; simp only [mapPt, Category.assoc]; simpa [Category.assoc] using hc)
  have := congrArg Subtype.val h
  exact (cancel_mono ι).1 this

theorem factorsThrough_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) :
    FactorsThrough (ι ≫ p) Q ↔ ∃ P : SchemeHomOver t f₀, FactorsThrough ι P ∧ mapPt p hp P = Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c ≫ ι, by rw [← hp, Category.assoc, ← Category.assoc ι, ← Category.assoc, hc]; exact Q.2⟩, ⟨c, rfl⟩, ?_⟩
    apply Subtype.ext; simp only [mapPt, Category.assoc]; simpa [Category.assoc] using hc
  · rintro ⟨P, ⟨c, hc⟩, rfl⟩
    exact ⟨c, by simp only [mapPt, ← Category.assoc, hc]⟩

include hp_hom hsub in
theorem sub {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q Q' : SchemeHomOver t f)
    (hQ : FactorsThrough (ι ≫ p) Q) (hQ' : FactorsThrough (ι ≫ p) Q') :
    FactorsThrough (ι ≫ p) (L.mul t Q Q') ∧ FactorsThrough (ι ≫ p) (L.inv t Q) := by
  rw [factorsThrough_iff p hp ι] at hQ hQ'
  obtain ⟨P, hP, hPQ⟩ := hQ; obtain ⟨P', hP', hPQ'⟩ := hQ'
  subst hPQ hPQ'
  constructor
  · rw [factorsThrough_iff p hp ι]; exact ⟨L₀.mul t P P', (hsub t P P' hP hP').1, hp_hom t P P'⟩
  · rw [factorsThrough_iff p hp ι]; exact ⟨L₀.inv t P, (hsub t P P hP hP).2, map_inv L₀ L p hp hp_hom t P⟩

include hp_hom in
private theorem _root_.P8IMGSUB.one (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough ι (L₀.one t))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : FactorsThrough (ι ≫ p) (L.one t) := by
  rw [factorsThrough_iff p hp ι]; exact ⟨L₀.one t, hone t, map_one L₀ L p hp hp_hom t⟩

p2m_export "P8IMGSUB" "one"
include hp_hom in
theorem torsion (n : ℕ) (htor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → nsmulPt L₀ t n P = L₀.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    nsmulPt L t n Q = L.one t := by
  rw [factorsThrough_iff p hp ι] at hQ
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  have hn : ∀ m : ℕ, mapPt p hp (nsmulPt L₀ t m P) = nsmulPt L t m (mapPt p hp P) := by
    intro m; induction m with
    | zero => exact map_one L₀ L p hp hp_hom t
    | succ m ih => simp only [nsmulPt]; rw [hp_hom, ih]
  rw [← hn, htor t P hP]; exact map_one L₀ L p hp hp_hom t

include hp in

theorem stable (α₀ : A₀ ⟶ A₀) (hα₀ : α₀ ≫ f₀ = f₀) (α : A ⟶ A) (hα : α ≫ f = f) (hcomm : p ≫ α = α₀ ≫ p)
    (hst : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → FactorsThrough ι (mapPt α₀ hα₀ P))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    FactorsThrough (ι ≫ p) (mapPt α hα Q) := by
  rw [factorsThrough_iff p hp ι] at hQ ⊢
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  refine ⟨mapPt α₀ hα₀ P, hst t P hP, ?_⟩
  apply Subtype.ext; simp only [mapPt, Category.assoc, hcomm]

include hp_hom hsub hdisj in

theorem exists_equiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∃ e : {P : SchemeHomOver t f₀ // FactorsThrough ι P} ≃ {Q : SchemeHomOver t f // FactorsThrough (ι ≫ p) Q},
      (∀ P, ((e P) : SchemeHomOver t f) = mapPt p hp P.1) := by
  refine ⟨Equiv.ofBijective (fun P => ⟨mapPt p hp P.1, (factorsThrough_iff p hp ι t _).2 ⟨P.1, P.2, rfl⟩⟩) ⟨?_, ?_⟩, fun P => rfl⟩
  · intro P P' h
    exact Subtype.ext (inj L₀ L p hp hp_hom ι hsub hdisj t P.1 P'.1 P.2 P'.2 (congrArg Subtype.val h))
  · rintro ⟨Q, hQ⟩
    obtain ⟨P, hP, rfl⟩ := (factorsThrough_iff p hp ι t Q).1 hQ
    exact ⟨⟨P, hP⟩, rfl⟩

theorem torsion' (n : ℕ) (htor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
      FactorsThrough ι P → nsmulPt L t n (mapPt p hp P) = L.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) (hQ : FactorsThrough (ι ≫ p) Q) :
    nsmulPt L t n Q = L.one t := by
  rw [factorsThrough_iff p hp ι] at hQ
  obtain ⟨P, hP, hPQ⟩ := hQ
  subst hPQ
  exact htor t P hP

end P8IMGSUB

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) (C₀ : A₀.ExtraLevel ℓ) :
    ∃ (A₀s : FakeEllipticCurve Λ N k₀)
      (as : A₀.A ⟶ A₀s.A) (has : as ≫ A₀s.f = A₀.f) (as' : A₀s.A ⟶ A₀.A) (has' : as' ≫ A₀.f = A₀s.f),
      FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨A₀, C₀⟩ A₀s as has as' has' ∧ Epi as ∧
      ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
          FactorsThrough C₀.levK P → mapPt φ hφ P = A₀.L.one t) →
        ∃! χ : SchemeHomOver A₀s.f A₀.f, as ≫ χ.1 = φ ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀s.f),
        mapPt χ.1 χ.2 (A₀s.L.mul t P Q) = A₀.L.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) := by
  classical
  have hO : IsOrder Λ := hΛ.1
  have hℓk : (ℓ : k₀) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff k₀ r ℓ).1 h
    exact hℓr ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) hℓ).1 hd).symm
  obtain ⟨A, f, L, act, hact, p, hp, ψ, hψ, hcomm, hbundle, hdim, hact_hom, hact_one, hact_mul, hact_add, htrace,
      hp_hom, hequiv, hfin, hflat, hlfp, hsurj, hEt, hrank, hker, hψ_hom, hψ_lin, hψp, hpψ, huniv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed k₀ A₀ hO ℓ hℓk C₀.K C₀.levK C₀.levK_closed
      C₀.levK_finite C₀.levK_flat C₀.levK_finitePresentation C₀.levK_one C₀.levK_sub C₀.levK_stable C₀.levK_torsion
  haveI := C₀.levK_closed
  haveI := A₀.lev_closed
  haveI := hfin

  have hdisj : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → mapPt p hp P = L.one t → P = A₀.L.one t :=
    fun t P hC hpP => C₀.levK_disjoint t P ((hker t P).1 hpP) hC
  haveI : IsFinite (A₀.lev ≫ p) := inferInstance
  have hlevf : (A₀.lev ≫ p) ≫ f = A₀.lev ≫ A₀.f := by rw [Category.assoc, hp]

  have hnat : ∀ (m : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k₀)) (Q : SchemeHomOver t f),
      pushPt (act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩) (hact _) Q = nsmulPt L t m Q := by
    intro m
    induction m with
    | zero =>
      intro hm T t Q
      have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) + ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ = ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ := by
        apply Subtype.ext; simp
      have h := hact_add ⟨_, hm⟩ ⟨_, hm⟩ t Q
      rw [h0] at h
      have := congrArg (L.mul t (L.inv t (pushPt (act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩) (hact _) Q))) h
      rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
      exact this.symm
    | succ m ih =>
      intro hm T t Q
      have hm' : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
        rw [this]; exact Λ.smul_mem _ hO.one_mem
      have e : (⟨(((m + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm'⟩ + ⟨1, hO.one_mem⟩ := by
        apply Subtype.ext; push_cast; rfl
      rw [e, hact_add, ih hm']
      have h1' : pushPt (act ⟨1, hO.one_mem⟩) (hact _) Q = Q := by
        apply Subtype.ext
        show Q.1 ≫ act ⟨1, hO.one_mem⟩ = Q.1
        rw [hact_one, Category.comp_id]
      rw [h1']
      rfl
  refine ⟨
    { A := A
      f := f
      L := L
      comm := hcomm
      bundle := hbundle
      dim_fibre := hdim
      act := act
      act_over := hact
      act_hom := hact_hom
      act_one := hact_one
      act_mul := hact_mul
      act_add := hact_add
      act_trace := htrace
      C := A₀.C
      lev := A₀.lev ≫ p
      lev_closed := P8IMGSUB.isClosedImmersion A₀.L L p hp hp_hom A₀.lev A₀.lev_sub hdisj
      lev_sub := fun t P Q hP hQ => P8IMGSUB.sub A₀.L L p hp hp_hom A₀.lev A₀.lev_sub t P Q hP hQ
      lev_one := fun t => P8IMGSUB.one A₀.L L p hp hp_hom A₀.lev A₀.lev_one t
      lev_torsion := fun t P hP => P8IMGSUB.torsion A₀.L L p hp hp_hom A₀.lev N A₀.lev_torsion t P hP
      lev_stable := fun x _ t P hP =>
        P8IMGSUB.stable p hp A₀.lev (A₀.act x) (A₀.act_over x) (act x) (hact x) (hequiv x).symm (A₀.lev_stable x) t P hP
      lev_finite := by rw [hlevf]; exact A₀.lev_finite
      lev_flat := by rw [hlevf]; exact A₀.lev_flat
      lev_finitePresentation := by rw [hlevf]; exact A₀.lev_finitePresentation
      lev_rank := fun s => by rw [hlevf]; exact A₀.lev_rank s
      lev_fibre := fun k' _ _ sk hN => by
        obtain ⟨e₀, he₀⟩ := A₀.lev_fibre k' sk hN
        obtain ⟨e₁, he₁⟩ := P8IMGSUB.exists_equiv A₀.L L p hp hp_hom A₀.lev A₀.lev_sub hdisj (geomPoint k' sk)
        refine ⟨e₀.trans e₁, fun x y => ?_⟩
        simp only [Equiv.trans_apply]
        rw [he₁, he₁, he₁, he₀, hp_hom] }, ?_⟩

  refine ⟨p, hp, ψ, hψ, ⟨hp_hom, hψ_hom, hequiv, hψ_lin, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro hℓ'
    constructor
    · have h := congrArg Subtype.val ((hψp A₀.f ⟨𝟙 _, Category.id_comp _⟩).trans
        (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt A₀ hO.one_mem ℓ hℓ' A₀.f ⟨𝟙 _, Category.id_comp _⟩).symm)
      simpa [mapPt, pushPt] using h
    · have h := congrArg Subtype.val ((hpψ f ⟨𝟙 _, Category.id_comp _⟩).trans (hnat ℓ hℓ' f ⟨𝟙 _, Category.id_comp _⟩).symm)
      simpa [mapPt, pushPt] using h
  · intro T t P; exact hker t P
  · intro T t P hP; exact (P8IMGSUB.factorsThrough_iff p hp A₀.lev t _).2 ⟨P, hP, rfl⟩
  · haveI := hflat; haveI := hsurj
    exact Flat.epi_of_flat_of_surjective p
  · intro φ hφ hφ_hom hkill
    exact huniv A₀.A A₀.f A₀.L φ hφ hφ_hom hkill

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq (solution)
