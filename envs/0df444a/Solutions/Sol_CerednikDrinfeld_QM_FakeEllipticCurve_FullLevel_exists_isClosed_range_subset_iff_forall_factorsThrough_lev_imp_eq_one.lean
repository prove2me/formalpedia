-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/edbabd57-6187-54a4-a256-7f6aad8a7848

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

universe u

namespace DisjLocus12

section PointAlgebra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_one (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 := by
  have hm := L.mul_natural t t' ψ hψ
  have h : schemeHomOverComp ψ hψ (L.one t) =
      L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t)) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hm _ _
  have : schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
    calc schemeHomOverComp ψ hψ (L.one t)
        = L.mul t' (L.one t') (schemeHomOverComp ψ hψ (L.one t)) := (L.one_mul t' _).symm
      _ = L.mul t' (L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)))
            (schemeHomOverComp ψ hψ (L.one t)) := by rw [L.inv_mul_cancel]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t)))
            (L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t))) := by rw [L.mul_assoc]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)) := by rw [← h]
      _ = L.one t' := L.inv_mul_cancel t' _
  exact congrArg Subtype.val this

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem comp_nsmulPt (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    ψ ≫ (nsmulPt L t n P).1 = (nsmulPt L t' n (schemeHomOverComp ψ hψ P)).1 := by
  induction n with
  | zero => exact comp_one L t t' ψ hψ
  | succ n ih =>
    simp only [nsmulPt]
    have := congrArg Subtype.val (L.mul_natural t t' ψ hψ (nsmulPt L t n P) P)
    rw [schemeHomOverComp_coe] at this
    rw [this]
    congr 2
    exact Subtype.ext (by rw [schemeHomOverComp_coe, ih])

theorem nsmulPt_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := comp_nsmulPt L f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (by simp)
  rw [hid] at h
  rw [← h, RelativeGroupLaw.schemeNsmul, nsmulPt_eq_nsmul]

end PointAlgebra

section FEC
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem pushPt_one (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act x) (E.act_over x) (E.L.one t)))) h
  rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem pushPt_nsmulPt (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n P) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) := by
  induction n with
  | zero => exact pushPt_one E x t
  | succ n ih => simp only [nsmulPt]; rw [E.act_hom, ih]

end FEC

section Locus
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ)

theorem schemeKerStr_eq : E.L.schemeKerStr m = pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ E.f := by
  show pullback.snd (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 = _
  have h1 : pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ E.f =
      pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 ≫ (E.L.schemeNsmul m ≫ E.f) := by rw [E.L.schemeNsmul_over]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, (E.L.one (𝟙 _)).2, Category.comp_id]

noncomputable def Q₀ : SchemeHomOver (E.L.schemeKerStr m) E.f :=
  ⟨pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1, (schemeKerStr_eq E m).symm⟩

@[scoped simp] theorem Q₀_coe : (Q₀ E m).1 = pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 := rfl

theorem coe_comp_schemeNsmul_of_nsmulPt_eq_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (hP : nsmulPt E.L t m P = E.L.one t) :
    P.1 ≫ E.L.schemeNsmul m = t ≫ (E.L.one (𝟙 _)).1 := by
  rw [← nsmulPt_coe, hP]
  exact (comp_one E.L (𝟙 _) t t (Category.comp_id _)).symm

end Locus

end DisjLocus12
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

namespace DisjLocus12

section Algebra
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem pushPt_act_congr {x y : ↥Λ} (h : x = y) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act y) (E.act_over y) P := by subst h; rfl

theorem pushPt_act_zero {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  have h := E.act_add 0 0 t P
  rw [pushPt_act_congr E (add_zero 0)] at h
  have := congrArg (E.L.mul t (E.L.inv t (pushPt (E.act 0) (E.act_over 0) P))) h
  rw [← E.L.mul_assoc, E.L.inv_mul_cancel, E.L.one_mul] at this
  exact this.symm

theorem pushPt_act_neg (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act (-x)) (E.act_over (-x)) P = E.L.inv t (pushPt (E.act x) (E.act_over x) P) := by
  letI := E.L.pointGroup t
  have h := E.act_add (-x) x t P
  rw [pushPt_act_congr E (neg_add_cancel x), pushPt_act_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pushPt_act_comp (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) P =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) P) := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, Category.assoc, E.act_mul x y h]

theorem natCast_mem (hΛ : IsOrder Λ) (m : ℕ) : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
  rw [this, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hΛ.one_mem m

theorem smul_mem (m : ℕ) (y : ↥Λ) : (m : ℚ) • (y : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem y.2 m

theorem pushPt_torsion (x : ↥Λ) (m : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    nsmulPt E.L t m (pushPt (E.act x) (E.act_over x) P) = E.L.one t := by
  rw [← pushPt_nsmulPt, hP, pushPt_one]

theorem pushPt_act_smul_eq_one (hΛ : IsOrder Λ) (m : ℕ) (y : ↥Λ) (hmy : (m : ℚ) • (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    pushPt (E.act ⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), hmy⟩) (E.act_over _) P = E.L.one t := by
  have hm := natCast_mem hΛ m
  have hxy : (((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem hm y.2
  have e : (⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), hmy⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ :=
    Subtype.ext (QuaternionAlgebra.coe_mul_eq_smul _ _).symm
  rw [pushPt_act_congr E e, pushPt_act_comp E ⟨_, hm⟩ y hxy,
    CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hΛ.one_mem m hm,
    pushPt_torsion E y m t P hP]

theorem pushPt_eq_of_congr (hΛ : IsOrder Λ) (m : ℕ) {x x' : ↥Λ}
    (h : ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) :
    pushPt (E.act x) (E.act_over x) P = pushPt (E.act x') (E.act_over x') P := by
  obtain ⟨y, hy⟩ := h
  have e : x = x' + ⟨(m : ℚ) • (y : ℍ[ℚ, a, b]), smul_mem m y⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_mk, ← hy]; abel
  rw [pushPt_act_congr E e, E.act_add, pushPt_act_smul_eq_one E hΛ m y _ t P hP, E.L.mul_one]

end Algebra
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

section Lattice
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem mem_span_smul_iff (m : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ↔
      ∃ y : ↥Λ, x = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  have hsmul : ∀ y : ℍ[ℚ, a, b], (m : ℤ) • y = (m : ℚ) • y := fun y => by
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨y, hy⟩, hsmul y⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, by simp [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨u, rfl⟩ := hx
      exact ⟨c • u, by rw [Submodule.coe_smul, smul_comm]⟩
  · rintro ⟨y, rfl⟩
    rw [← hsmul]
    exact Submodule.subset_span ⟨y, y.2, rfl⟩

end Lattice
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

end DisjLocus12
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

namespace DisjLocus12

section Extra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_pow (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = (letI := L.pointGroup t; P ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nsmulPt]
    rw [pow_succ, ← ih]
    rfl

theorem nsmulPt_mul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t (a * b) P = nsmulPt L t a (nsmulPt L t b P) := by
  letI := L.pointGroup t
  rw [nsmulPt_pow, nsmulPt_pow, nsmulPt_pow]
  exact pow_mul' P a b

theorem nsmulPt_one_pt (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  rw [nsmulPt_eq_nsmul]; exact RelativeGroupLaw.nsmul_unit _ _ _

end Extra
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

section SectionAt
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)

theorem pushPt_nsmulPt_sectionAt_coe (x : ↥Λ) (c : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (k : Type) [Field k] (sk : S →+* k) :
    (pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) c (FakeEllipticCurve.sectionAt P k sk))).1 =
      geomPoint k sk ≫ (pushPt (E.act x) (E.act_over x) (nsmulPt E.L (𝟙 _) c P)).1 := by
  simp only [pushPt, mapPt_coe]
  rw [← Category.assoc, comp_nsmulPt E.L (𝟙 _) (geomPoint k sk) (geomPoint k sk) (Category.comp_id _) c P]
  rfl

theorem nsmulPt_sectionAt (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (n : ℕ)
    (hP : nsmulPt E.L (𝟙 _) n P = E.L.one _) (k : Type) [Field k] (sk : S →+* k) :
    nsmulPt E.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt P k sk) = E.L.one (geomPoint k sk) := by
  apply Subtype.ext
  have h := comp_nsmulPt E.L (𝟙 _) (geomPoint k sk) (geomPoint k sk) (Category.comp_id _) n P
  rw [hP, comp_one E.L (𝟙 _) (geomPoint k sk) (geomPoint k sk) (Category.comp_id _)] at h
  exact h.symm

end SectionAt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

end DisjLocus12
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one.DisjLocus12"

open DisjLocus12 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    {S : Type} [CommRing S] (hN : IsUnit ((N : ℕ) : S)) (hm : IsUnit ((m : ℕ) : S))
    (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) :
    ∃ V : (Spec (CommRingCat.of S)).Opens, IsClosed (V : Set ↥(Spec (CommRingCat.of S))) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
        Set.range (geomPoint k sk) ⊆ (V : Set ↥(Spec (CommRingCat.of S))) ↔
          ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
            FactorsThrough E.lev
              (pushPt (E.act x) (E.act_over x)
                (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
            pushPt (E.act x) (E.act_over x)
                (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)) ∧
      (¬ ℓ ∣ N → V = ⊤) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓpos : 0 < ℓ := hℓ.pos
  have hdiv : ℓ * (m / ℓ) = m := Nat.mul_div_cancel' hℓm

  have hPℓ : ∀ (k : Type) [Field k] (sk : S →+* k),
      nsmulPt E.L (geomPoint k sk) ℓ (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
        E.L.one (geomPoint k sk) := by
    intro k _ sk
    rw [← nsmulPt_mul, hdiv]
    exact nsmulPt_sectionAt E P.P m P.torsion k sk
  by_cases hℓN : ℓ ∣ N
  swap
  ·
    refine ⟨⊤, by simp, fun k _ _ sk => ?_, fun _ => rfl⟩
    refine ⟨fun _ x _ hFT => ?_, fun _ => by simp⟩
    letI := E.L.pointGroup (geomPoint k sk)
    have hQℓ := pushPt_torsion E x ℓ _ _ (hPℓ k sk)
    have hQN := E.lev_torsion _ _ hFT
    rw [nsmulPt_pow] at hQℓ hQN
    have hcop : Nat.gcd ℓ N = 1 := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓN
    have h := pow_gcd_eq_one.2 ⟨hQℓ, hQN⟩
    rwa [hcop, pow_one] at h

  have hn : IsUnit (((m * N : ℕ) : ℕ) : S) := by rw [Nat.cast_mul]; exact hm.mul hN
  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E (m * N) hn
  haveI := hfin; haveI := het
  haveI := E.lev_closed; haveI := E.lev_flat; haveI := E.lev_finitePresentation
  obtain ⟨UC, eC, hUCcl, -, hUC⟩ :=
    E.L.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one (m * N) E.lev
      (fun t Q hQ => by rw [nsmulPt_mul, E.lev_torsion t Q hQ, nsmulPt_one_pt])

  let σ : ↥Λ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := fun x =>
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L (𝟙 _) (m / ℓ) P.P)
  have hσtor : ∀ x, nsmulPt E.L (𝟙 _) (m * N) (σ x) = E.L.one _ := by
    intro x
    have h1 : nsmulPt E.L (𝟙 _) m (σ x) = E.L.one _ := by
      apply pushPt_torsion
      rw [← nsmulPt_mul, Nat.mul_comm m (m / ℓ), nsmulPt_mul, P.torsion, nsmulPt_one_pt]
    rw [Nat.mul_comm m N, nsmulPt_mul, h1, nsmulPt_one_pt]
  have hσw : ∀ x, (σ x).1 ≫ E.L.schemeNsmul (m * N) =
      𝟙 _ ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := fun x =>
    coe_comp_schemeNsmul_of_nsmulPt_eq_one E (m * N) (𝟙 _) (σ x) (hσtor x)
  let s : ↥Λ → (Spec (CommRingCat.of S) ⟶ E.L.schemeKer (m * N)) := fun x =>
    pullback.lift (σ x).1 (𝟙 _) (hσw x)
  have hs_fst : ∀ x, s x ≫ pullback.fst (E.L.schemeNsmul (m * N)) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 =
      (σ x).1 := fun x => pullback.lift_fst _ _ _
  have hs_snd : ∀ x, s x ≫ E.L.schemeKerStr (m * N) = 𝟙 _ := fun x => pullback.lift_snd _ _ _
  have h1w : (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.L.schemeNsmul (m * N) =
      𝟙 _ ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
    coe_comp_schemeNsmul_of_nsmulPt_eq_one E (m * N) (𝟙 _) _ (nsmulPt_one_pt _ _ _)
  let s₁ : Spec (CommRingCat.of S) ⟶ E.L.schemeKer (m * N) := pullback.lift (E.L.one (𝟙 _)).1 (𝟙 _) h1w
  have hs₁_fst : s₁ ≫ pullback.fst (E.L.schemeNsmul (m * N)) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 =
      (E.L.one (𝟙 _)).1 := pullback.lift_fst _ _ _
  have hs₁_snd : s₁ ≫ E.L.schemeKerStr (m * N) = 𝟙 _ := pullback.lift_snd _ _ _

  have hOx : ∀ x : ↥Λ, ∃ O : Set ↥(Spec (CommRingCat.of S)), IsClopen O ∧
      ∀ {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of S)), Set.range g ⊆ O ↔ g ≫ s x = g ≫ s₁ := by
    intro x
    obtain ⟨hc, hp⟩ := AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
      (E.L.schemeKerStr (m * N)) (s x) s₁ (hs_snd x) hs₁_snd
    exact ⟨_, hc, hp⟩
  choose O hOc hOp using hOx

  let Z : ↥Λ → Set ↥(Spec (CommRingCat.of S)) := fun x => (s x).base ⁻¹' (UC : Set ↥(E.L.schemeKer (m * N)))
  have hZcl : ∀ x, IsClosed (Z x) := fun x => hUCcl.preimage (s x).continuous
  have hZop : ∀ x, IsOpen (Z x) := fun x => UC.2.preimage (s x).continuous

  let ℓΛ : Submodule ℤ ℍ[ℚ, a, b] := Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))
  let H : AddSubgroup ↥Λ.toAddSubgroup := ℓΛ.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup
  have hHidx : H.index = ℓ ^ 4 := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ hℓpos
  haveI : Fintype (↥Λ.toAddSubgroup ⧸ H) := AddSubgroup.fintypeOfIndexNeZero (by rw [hHidx]; positivity)
  have memH : ∀ h : ↥Λ.toAddSubgroup, h ∈ H ↔ ∃ y : ↥Λ, (h : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro h
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    exact mem_span_smul_iff ℓ _
  let rep : ↥Λ.toAddSubgroup ⧸ H → ↥Λ := fun c => ⟨(Quotient.out c : ↥Λ.toAddSubgroup).1, (Quotient.out c).2⟩
  let R' : Finset ↥Λ := (Finset.univ.image rep).filter (fun r => (r : ℍ[ℚ, a, b]) ∈ L₀)
  have hrep : ∀ x : ↥Λ, ∃ y : ↥Λ, ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) =
      (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H (⟨x.1, x.2⟩ : ↥Λ.toAddSubgroup)
    obtain ⟨y, hy⟩ := (memH h).1 h.2
    refine ⟨y, ?_⟩
    have : ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) + (h : ↥Λ.toAddSubgroup) := by
      show ((Quotient.out (QuotientAddGroup.mk (⟨x.1, x.2⟩ : ↥Λ.toAddSubgroup)) : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = _
      rw [hh]; rfl
    rw [this, ← hy]; abel

  let Vset : Set ↥(Spec (CommRingCat.of S)) := ⋂ r ∈ R', ((Z r)ᶜ ∪ O r)
  have hVop : IsOpen Vset := isOpen_biInter_finset fun r _ => (hZcl r).isOpen_compl.union (hOc r).isOpen
  have hVcl : IsClosed Vset := isClosed_biInter fun r _ => (hZop r).isClosed_compl.union (hOc r).isClosed
  refine ⟨⟨Vset, hVop⟩, hVcl, fun k _ _ sk => ?_, fun h => (h hℓN).elim⟩

  have hrange : ∀ Y : Set ↥(Spec (CommRingCat.of S)),
      Set.range (geomPoint k sk) ⊆ Y ↔ (geomPoint k sk).base default ∈ Y := by
    intro Y
    constructor
    · intro h; exact h ⟨default, rfl⟩
    · rintro h _ ⟨w, rfl⟩; rw [Subsingleton.elim w default]; exact h
  have hpt : ∀ r : ↥Λ, (Set.range (geomPoint k sk) ⊆ (Z r)ᶜ ∪ O r) ↔
      (FactorsThrough E.lev
          (pushPt (E.act r) (E.act_over r) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
        pushPt (E.act r) (E.act_over r) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
          E.L.one (geomPoint k sk)) := by
    intro r
    have hQ1 := pushPt_nsmulPt_sectionAt_coe E r (m / ℓ) P.P k sk
    have hZr : (geomPoint k sk).base default ∈ Z r ↔ FactorsThrough E.lev
        (pushPt (E.act r) (E.act_over r) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) := by
      show (s r).base ((geomPoint k sk).base default) ∈ (UC : Set ↥(E.L.schemeKer (m * N))) ↔ _
      rw [hUC]
      constructor
      · intro h
        refine ⟨geomPoint k sk ≫ s r, by rw [Category.assoc, hs_fst, hQ1], ?_⟩
        rintro _ ⟨w, rfl⟩
        rw [Subsingleton.elim w default, Scheme.Hom.comp_apply]
        exact h
      · rintro ⟨κ, hκ, hκU⟩
        have hκs : κ = geomPoint k sk ≫ s r := by
          apply pullback.hom_ext
          · rw [hκ, Category.assoc, hs_fst, hQ1]
          · rw [Category.assoc]
            change κ ≫ E.L.schemeKerStr (m * N) = geomPoint k sk ≫ s r ≫ E.L.schemeKerStr (m * N)
            rw [hs_snd, Category.comp_id, schemeKerStr_eq, ← Category.assoc, hκ]
            exact (pushPt (E.act r) (E.act_over r)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))).2
        rw [hκs] at hκU
        have := hκU ⟨default, rfl⟩
        rwa [Scheme.Hom.comp_apply] at this
    have hOr : (geomPoint k sk).base default ∈ O r ↔
        pushPt (E.act r) (E.act_over r) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) =
          E.L.one (geomPoint k sk) := by
      rw [← hrange, hOp r (geomPoint k sk)]
      constructor
      · intro h
        apply Subtype.ext
        rw [hQ1]
        have h2 := congrArg (fun φ => φ ≫ pullback.fst (E.L.schemeNsmul (m * N)) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) h
        simp only [Category.assoc, hs_fst, hs₁_fst] at h2
        rw [h2]
        exact comp_one E.L (𝟙 _) (geomPoint k sk) (geomPoint k sk) (Category.comp_id _)
      · intro h
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hs_fst, hs₁_fst, ← hQ1, h]
          exact (comp_one E.L (𝟙 _) (geomPoint k sk) (geomPoint k sk) (Category.comp_id _)).symm
        · rw [Category.assoc, Category.assoc, hs_snd, hs₁_snd]
    rw [hrange, Set.mem_union, Set.mem_compl_iff, hZr, hOr]
    exact imp_iff_not_or.symm
  have hV : Set.range (geomPoint k sk) ⊆ Vset ↔ ∀ r ∈ R', Set.range (geomPoint k sk) ⊆ (Z r)ᶜ ∪ O r := by
    simp only [Vset, Set.subset_iInter_iff]
  show Set.range (geomPoint k sk) ⊆ Vset ↔ _
  rw [hV]
  constructor
  · intro hR x hx hFT
    obtain ⟨y, hy⟩ := hrep x
    have hrL : ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) ∈ L₀ := by
      have e : ((rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) : ↥Λ) : ℍ[ℚ, a, b]) =
          (x : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by rw [← hy]; abel
      rw [e]; exact L₀.add_mem hx (hℓL₀ y)
    have hrR' : rep (QuotientAddGroup.mk ⟨x.1, x.2⟩) ∈ R' :=
      Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, hrL⟩
    have hcongr := pushPt_eq_of_congr E hO ℓ ⟨y, hy⟩ _ _ (hPℓ k sk)
    rw [← hcongr] at hFT ⊢
    exact (hpt _).1 (hR _ hrR') hFT
  · intro h r hr
    obtain ⟨-, hrL⟩ := Finset.mem_filter.1 hr
    exact (hpt r).2 (h r hrL)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_lev_imp_eq_one (solution)
