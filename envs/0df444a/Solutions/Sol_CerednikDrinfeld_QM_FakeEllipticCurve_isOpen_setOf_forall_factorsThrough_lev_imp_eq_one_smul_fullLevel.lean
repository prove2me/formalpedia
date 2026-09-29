-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/32270c59-9cc8-5c4b-9a93-b3b7645cb433

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

universe u

namespace GenLocus10

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

theorem Q₀_torsion : nsmulPt E.L (E.L.schemeKerStr m) m (Q₀ E m) = E.L.one (E.L.schemeKerStr m) := by
  apply Subtype.ext
  rw [nsmulPt_coe, Q₀_coe, pullback.condition]
  exact comp_one E.L (𝟙 _) _ _ (Category.comp_id _)

theorem xQ₀_torsion (x : ↥Λ) :
    nsmulPt E.L (E.L.schemeKerStr m) m (pushPt (E.act x) (E.act_over x) (Q₀ E m)) = E.L.one (E.L.schemeKerStr m) := by
  rw [← pushPt_nsmulPt, Q₀_torsion, pushPt_one]

noncomputable def sx (x : ↥Λ) : E.L.schemeKer m ⟶ E.L.schemeKer m :=
  pullback.lift (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 (E.L.schemeKerStr m)
    (coe_comp_schemeNsmul_of_nsmulPt_eq_one E m _ _ (xQ₀_torsion E m x))

noncomputable def s1 : E.L.schemeKer m ⟶ E.L.schemeKer m :=
  pullback.lift (E.L.one (E.L.schemeKerStr m)).1 (E.L.schemeKerStr m)
    (coe_comp_schemeNsmul_of_nsmulPt_eq_one E m _ _ (by
      rw [nsmulPt_eq_nsmul]; exact RelativeGroupLaw.nsmul_unit _ _ _))

theorem sx_snd (x : ↥Λ) : sx E m x ≫ E.L.schemeKerStr m = E.L.schemeKerStr m := pullback.lift_snd _ _ _
theorem s1_snd : s1 E m ≫ E.L.schemeKerStr m = E.L.schemeKerStr m := pullback.lift_snd _ _ _
theorem sx_fst (x : ↥Λ) : sx E m x ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 =
    (pushPt (E.act x) (E.act_over x) (Q₀ E m)).1 := pullback.lift_fst _ _ _
theorem s1_fst : s1 E m ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 _)).1 =
    (E.L.one (E.L.schemeKerStr m)).1 := pullback.lift_fst _ _ _

end Locus

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace GenLocus10

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

private theorem _root_.GenLocus10.smul_mem (m : ℕ) (y : ↥Λ) : (m : ℚ) • (y : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem y.2 m

p2m_export "GenLocus10" "smul_mem"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace GenLocus10

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

end GenLocus10
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace GLUEaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem mapPt_mapPt {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_injective_of_isIso {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) [IsIso φ]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : mapPt φ hφ P = mapPt φ hφ Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt] at this
  exact (cancel_mono φ).1 this

end GLUEaux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace GLUEact

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

private theorem _root_.GLUEact.natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

p2m_export "GLUEact" "natCast_mem"
theorem act_zero_apply (E : FakeEllipticCurve Λ N S) (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  apply GLUEaux.eq_one_of_mul_self
  have := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ + ⟨0, h0⟩ : ↥Λ) = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at this
  exact this.symm

theorem act_natCast_apply (E : FakeEllipticCurve Λ N S) (hΛ : IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have e : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = ⟨0, by simpa using natCast_mem hΛ 0⟩ := by
      apply Subtype.ext; simp
    rw [show pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩) (E.act_over _) P =
        pushPt (E.act ⟨0, by simpa using natCast_mem hΛ 0⟩) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    exact act_zero_apply E _ t P
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [show pushPt (E.act ⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩) (E.act_over _) P =
        pushPt (E.act (⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩)) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    rw [E.act_add, ih]
    simp only [nsmulPt]
    congr 1
    simp only [pushPt]
    rw [GLUEaux.mapPt_congr (E.act_one hΛ.one_mem) _ (by simp) P]
    apply Subtype.ext; simp [mapPt]

end GLUEact
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  calc L.inv t (L.inv t x) = L.mul t (L.inv t (L.inv t x)) (L.one t) := (L.mul_one t _).symm
    _ = L.mul t (L.inv t (L.inv t x)) (L.mul t (L.inv t x) x) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t (L.inv t (L.inv t x)) (L.inv t x)) x := by rw [L.mul_assoc]
    _ = x := by rw [L.inv_mul_cancel, L.one_mul]

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  have := L.inv_mul_cancel t (L.inv t x)
  rwa [inv_inv] at this

theorem eq_of_mul_inv_eq_one {x y : SchemeHomOver t f} (h : L.mul t x (L.inv t y) = L.one t) : x = y := by
  have := congrArg (fun z => L.mul t z y) h
  rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem nsmulPt_add (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + m) P = L.mul t (nsmulPt L t n P) (nsmulPt L t m P) := by
  induction m with
  | zero => simp [nsmulPt, L.mul_one]
  | succ m ih => rw [Nat.add_succ]; simp only [nsmulPt]; rw [ih, L.mul_assoc]

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

theorem nsmulPt_mul (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n * m) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => simp [nsmulPt]
  | succ n ih => rw [Nat.succ_mul, nsmulPt_add, ih]; simp only [nsmulPt]

theorem nsmulPt_mod_eq_one {n m : ℕ} (P : SchemeHomOver t f)
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : nsmulPt L t (n % m) P = L.one t := by
  have e : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have := hn
  rw [e, nsmulPt_add, nsmulPt_mul, hm, nsmulPt_one_pt, L.one_mul] at this
  exact this

theorem eq_one_of_nsmulPt_eq_one_of_coprime {r N : ℕ} (hc : Nat.Coprime r N) (P : SchemeHomOver t f)
    (hr : nsmulPt L t r P = L.one t) (hN : nsmulPt L t N P = L.one t) : P = L.one t := by
  have key : ∀ a b : ℕ, nsmulPt L t a P = L.one t → nsmulPt L t b P = L.one t → nsmulPt L t (Nat.gcd a b) P = L.one t := by
    intro a b
    refine Nat.gcd.induction a b (fun n _ hn => by simpa using hn) (fun m n _ ih hm hn => ?_)
    rw [Nat.gcd_rec]
    exact ih (nsmulPt_mod_eq_one L t P hn hm) hm
  have := key r N hr hN
  rw [hc] at this
  simpa [nsmulPt, L.one_mul] using this

end GLUEgrp
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

namespace T4Aux

section GroupLaw
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul]; exact L.nsmul_natural t t' ψ hψ n P

theorem one_coe_eq (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← this]; rfl

theorem coe_comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : P.1 ≫ L.schemeNsmul n = (nsmulPt L t n P).1 := by
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := by
    apply Subtype.ext; simp [RelativeGroupLaw.idPoint]
  have := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hP] at this
  rw [nsmulPt_eq_nsmul, ← this]; rfl

theorem exists_comp_fst_eq_iff_nsmulPt_eq_one (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (∃ κ : T ⟶ L.schemeKer n,
        κ ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = P.1) ↔
      nsmulPt L t n P = L.one t := by
  have he : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  constructor
  · rintro ⟨κ, hκ⟩
    apply Subtype.ext
    have hsnd : κ ≫ pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = t := by
      have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
          pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
            = pullback.fst _ _ ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
          _ = (pullback.fst _ _ ≫ L.schemeNsmul n) ≫ f := (Category.assoc _ _ _).symm
          _ = (pullback.snd _ _ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by rw [pullback.condition]
          _ = pullback.snd _ _ := by rw [Category.assoc, he, Category.comp_id]
      rw [← P.2, ← hκ, Category.assoc, h1]
    rw [← coe_comp_schemeNsmul, one_coe_eq, ← hκ, Category.assoc, pullback.condition, ← Category.assoc, hsnd]
  · intro h
    refine ⟨pullback.lift P.1 t ?_, pullback.lift_fst _ _ _⟩
    rw [coe_comp_schemeNsmul, h, one_coe_eq]

theorem nsmulPt_eq_one_comp (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f)
    (h : nsmulPt L t n P = L.one t) : nsmulPt L t' n (schemeHomOverComp ψ hψ P) = L.one t' := by
  rw [← nsmulPt_natural, h]; exact L.one_natural t t' ψ hψ

theorem nsmulPt_eq_pow (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t; nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem nsmulPt_one' (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  have := nsmulPt_eq_pow L t n (L.one t)
  rw [this]; exact one_pow n

private theorem _root_.T4Aux.nsmulPt_mul (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P Q : SchemeHomOver t f) :
    nsmulPt L t n (L.mul t P Q) = L.mul t (nsmulPt L t n P) (nsmulPt L t n Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := hc t }
  have h1 := nsmulPt_eq_pow L t n (L.mul t P Q)
  have h2 := nsmulPt_eq_pow L t n P
  have h3 := nsmulPt_eq_pow L t n Q
  rw [h1, h2, h3]; exact mul_pow P Q n

p2m_export "T4Aux" "nsmulPt_mul"
theorem nsmulPt_inv (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n (L.inv t P) = L.inv t (nsmulPt L t n P) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := hc t }
  have h1 := nsmulPt_eq_pow L t n (L.inv t P)
  have h2 := nsmulPt_eq_pow L t n P
  rw [h1, h2]; exact inv_pow P n

private theorem _root_.T4Aux.pushPt_nsmulPt (L : RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    pushPt φ hφ (nsmulPt L t n P) = nsmulPt L t n (pushPt φ hφ P) := by
  have hone : pushPt φ hφ (L.one t) = L.one t := by
    letI := L.pointGroup t
    have h := hhom t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have : pushPt φ hφ (L.one t) * pushPt φ hφ (L.one t) = pushPt φ hφ (L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  induction n with
  | zero => exact hone
  | succ n ih => show pushPt φ hφ (L.mul t _ _) = L.mul t _ _; rw [hhom, ih]

p2m_export "T4Aux" "pushPt_nsmulPt"

def castPt {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (P : SchemeHomOver t f) :
    SchemeHomOver t' f := ⟨P.1, by rw [← h]; exact P.2⟩

@[scoped simp] theorem castPt_coe {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (P : SchemeHomOver t f) : (castPt h P).1 = P.1 := rfl

theorem castPt_mul (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)}
    (h : t = t') (P Q : SchemeHomOver t f) :
    castPt h (L.mul t P Q) = L.mul t' (castPt h P) (castPt h Q) := by
  subst h; rfl

theorem castPt_injective {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    Function.Injective (castPt (f := f) h) := by
  intro P Q hPQ; apply Subtype.ext
  have := congrArg Subtype.val hPQ
  simpa only [castPt_coe] using this

theorem mapPt_nsmulPt {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  have hone : mapPt φ hφ (L.one t) = L'.one t := by
    letI := L'.pointGroup t
    have h := hhom t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  induction n with
  | zero => exact hone
  | succ n ih => show mapPt φ hφ (L.mul t _ _) = L'.mul t _ _; rw [hhom, ih]

end GroupLaw
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

section Hom

variable {B B₀ : Type u} [CommRing B] [CommRing B₀] (φ : B →+* B₀)
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
  {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
  (g : A₀ ⟶ A) (hgw : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom φ))

def gPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of B₀)} (P : SchemeHomOver t f₀) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hgw, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of B₀)} (P : SchemeHomOver t f₀) :
    (gPt φ g hgw P).1 = P.1 ≫ g := rfl

variable (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
    gPt φ g hgw (L₀.mul t P Q) = L.mul _ (gPt φ g hgw P) (gPt φ g hgw Q))

include hmul in
theorem gPt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) :
    gPt φ g hgw (L₀.one t) = L.one _ := by
  letI := L.pointGroup (t ≫ Spec.map (CommRingCat.ofHom φ))
  have h := hmul t (L₀.one t) (L₀.one t)
  rw [L₀.one_mul] at h

  have : gPt φ g hgw (L₀.one t) * gPt φ g hgw (L₀.one t) = gPt φ g hgw (L₀.one t) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

include hmul in
theorem gPt_nsmulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (n : ℕ) (P : SchemeHomOver t f₀) :
    gPt φ g hgw (nsmulPt L₀ t n P) = nsmulPt L _ n (gPt φ g hgw P) := by
  induction n with
  | zero => exact gPt_one φ L L₀ g hgw hmul t
  | succ n ih => show gPt φ g hgw (L₀.mul t _ _) = L.mul _ _ _; rw [hmul, ih]

include hmul in
theorem gPt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t f₀) :
    gPt φ g hgw (L₀.inv t P) = L.inv _ (gPt φ g hgw P) := by
  letI := L.pointGroup (t ≫ Spec.map (CommRingCat.ofHom φ))
  have h := hmul t (L₀.inv t P) P
  rw [L₀.inv_mul_cancel, gPt_one φ L L₀ g hgw hmul] at h

  exact (eq_inv_of_mul_eq_one_left h.symm)

end Hom
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10"

end T4Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.T4Aux"

namespace KLAux

universe v in

theorem comp_inv {R : Type v} [CommRing R] {A : Scheme.{v}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t P) = L.inv t' (schemeHomOverComp ψ hψ P) := by
  letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.inv t P) P
  rw [L.inv_mul_cancel] at h
  have h1 : schemeHomOverComp ψ hψ (L.one t) = L.one t' := Subtype.ext (GenLocus10.comp_one L t t' ψ hψ)
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem eq_smul_of_mul_coe {a b : ℚ} (z y : ℍ[ℚ, a, b]) (ℓ m' : ℕ) (hm' : m' ≠ 0)
    (h : z * (((m' : ℕ) : ℚ) : ℍ[ℚ, a, b]) = (((ℓ * m' : ℕ)) : ℚ) • y) : z = (ℓ : ℚ) • y := by
  have h1 : ((m' : ℕ) : ℚ) • z = ((m' : ℕ) : ℚ) • ((ℓ : ℚ) • y) := by
    rw [← QuaternionAlgebra.mul_coe_eq_smul, h, smul_smul, Nat.cast_mul, mul_comm]
  exact smul_right_injective ℍ[ℚ, a, b] (Nat.cast_ne_zero.2 hm') h1

end KLAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.T4Aux"

section TRANSVERSAL
open GenLocus10 T4Aux

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) :
    IsOpen {p : PrimeSpectrum S |
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), RingHom.ker sk = p.asIdeal →
        ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
          FactorsThrough E.lev
            (pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
          pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)} := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨m', hm'⟩ := hℓm
  have hℓpos : 0 < ℓ := hℓ.pos
  have hdiv : m / ℓ = m' := by rw [hm', Nat.mul_div_cancel_left _ hℓpos]
  have hℓu : IsUnit ((ℓ : ℕ) : S) := by
    have : ((m : ℕ) : S) = (ℓ : S) * (m' : S) := by rw [hm']; push_cast; ring
    rw [this] at hm; exact isUnit_of_mul_isUnit_left hm
  obtain ⟨hfin, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓu
  haveI := hfin; haveI := het
  obtain ⟨ρ, hρL, hρadd, hρsurj, hρinj⟩ :=
    QuaternionAlgebra.IsOrder.exists_zmod_prod_section_of_relIndex_eq_sq Λ hO ℓ hℓ L₀ hL₀ hℓL₀ hL₀_index

  let R₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := nsmulPt E.L _ (m / ℓ) P.P
  have hR₀ℓ : nsmulPt E.L _ ℓ R₀ = E.L.one _ := by
    show nsmulPt E.L _ ℓ (nsmulPt E.L _ (m / ℓ) P.P) = _
    rw [hdiv, ← GLUEgrp.nsmulPt_mul]
    have : ℓ * m' = m := hm'.symm
    rw [this]; exact P.torsion
  let Rx : ↥Λ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := fun x => pushPt (E.act x) (E.act_over x) R₀
  have hRx_def : ∀ x, Rx x = pushPt (E.act x) (E.act_over x) R₀ := fun x => rfl
  have hRxℓ : ∀ x, nsmulPt E.L _ ℓ (Rx x) = E.L.one _ := by
    intro x; rw [hRx_def, ← GenLocus10.pushPt_nsmulPt, hR₀ℓ, GenLocus10.pushPt_one]
  have hRx_congr : ∀ x x' : ↥Λ, (∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) →
      Rx x = Rx x' := fun x x' h => GenLocus10.pushPt_eq_of_congr E hO ℓ h _ R₀ hR₀ℓ
  have hRx_add : ∀ x y : ↥Λ, Rx (x + y) = E.L.mul _ (Rx x) (Rx y) := fun x y => E.act_add x y _ R₀
  have hRx_neg : ∀ x : ↥Λ, Rx (-x) = E.L.inv _ (Rx x) := fun x => GenLocus10.pushPt_act_neg E x _ R₀
  have hRx_zero : Rx 0 = E.L.one _ := GenLocus10.pushPt_act_zero E _ R₀
  have hRx_act : ∀ y x : ↥Λ, pushPt (E.act y) (E.act_over y) (Rx x) =
      Rx ⟨(y : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hO.mul_mem y.2 x.2⟩ :=
    fun y x => (GenLocus10.pushPt_act_comp E y x (hO.mul_mem y.2 x.2) _ R₀).symm
  let σ : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := fun v => Rx (ρ v)
  have hσ_def : ∀ v, σ v = Rx (ρ v) := fun v => rfl
  have hσ : ∀ v, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) ℓ (σ v) = E.L.one (𝟙 (Spec (CommRingCat.of S))) :=
    fun v => hRxℓ _
  have hσ_add : ∀ v w, σ (v + w) = E.L.mul _ (σ v) (σ w) := by
    intro v w
    obtain ⟨y, hy⟩ := hρadd v w
    show Rx (ρ (v + w)) = E.L.mul _ (Rx (ρ v)) (Rx (ρ w))
    rw [← hRx_add]
    apply hRx_congr
    exact ⟨y, by rw [← hy, Submodule.coe_add]; abel⟩
  have hσ_neg : ∀ v, σ (-v) = E.L.inv _ (σ v) := by
    intro v
    have h0 : σ 0 = E.L.one _ := by
      obtain ⟨v₀, y, hy⟩ := hρsurj 0 L₀.zero_mem
      have h1 : Rx (ρ v₀) = E.L.one _ := by
        rw [← hRx_zero]; apply hRx_congr; exact ⟨-y, by rw [Submodule.coe_neg, smul_neg, ← hy, Submodule.coe_zero]; abel⟩

      letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
      have h2 : σ (0 + 0) = E.L.mul _ (σ 0) (σ 0) := hσ_add 0 0
      rw [add_zero] at h2
      exact GLUEaux.eq_one_of_mul_self E.L _ _ h2.symm
    letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
    have h3 : E.L.mul _ (σ (-v)) (σ v) = E.L.one _ := by rw [← hσ_add, neg_add_cancel, h0]
    exact eq_inv_of_mul_eq_one_left h3

  let bcT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f → SchemeHomOver t E.f :=
    fun t R => schemeHomOverComp t (Category.comp_id _) R
  have bcT_val : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R), (bcT t R).1 = t ≫ R.1 := fun t R => rfl
  have bcT_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), bcT t (E.L.one _) = E.L.one t :=
    fun t => E.L.one_natural _ _ t (Category.comp_id _)
  have bcT_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R R'),
      bcT t (E.L.mul _ R R') = E.L.mul t (bcT t R) (bcT t R') :=
    fun t R R' => E.L.mul_natural _ _ t (Category.comp_id _) R R'
  have bcT_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (R),
      bcT t (E.L.inv _ R) = E.L.inv t (bcT t R) :=
    fun t R => KLAux.comp_inv E.L _ _ t (Category.comp_id _) R
  have bcT_nsmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (R),
      bcT t (nsmulPt E.L _ n R) = nsmulPt E.L t n (bcT t R) := by
    intro T t n R
    induction n with
    | zero => exact bcT_one t
    | succ n ih => show schemeHomOverComp _ _ (E.L.mul _ _ _) = _; rw [E.L.mul_natural]; simp only [nsmulPt]; rw [← ih]
  have bcT_act : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : ↥Λ) (R),
      bcT t (pushPt (E.act x) (E.act_over x) R) = pushPt (E.act x) (E.act_over x) (bcT t R) := by
    intro T t x R; apply Subtype.ext; simp [bcT, schemeHomOverComp, pushPt, mapPt, Category.assoc]
  have hsecRx : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ),
      bcT (geomPoint k sk) (Rx x) =
        pushPt (E.act x) (E.act_over x) (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) := by
    intro k _ _ sk x
    show bcT (geomPoint k sk) (pushPt (E.act x) (E.act_over x) (nsmulPt E.L _ (m / ℓ) P.P)) = _
    rw [bcT_act, bcT_nsmul]; rfl

  have hinj_geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x x' : ↥Λ),
      bcT (geomPoint k sk) (Rx x) = bcT (geomPoint k sk) (Rx x') →
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (x' : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro k _ _ sk x x' h
    have hmk : ((m : ℕ) : k) ≠ 0 := by
      have := (hm.map sk).ne_zero; rwa [map_natCast] at this
    have hm'0 : m' ≠ 0 := by rintro rfl; apply hmk; simp [hm']
    set Q := bcT (geomPoint k sk) R₀ with hQ
    have hQℓ : nsmulPt E.L _ ℓ Q = E.L.one _ := by rw [hQ, ← bcT_nsmul, hR₀ℓ, bcT_one]
    have h1 : pushPt (E.act x) (E.act_over x) Q = pushPt (E.act x') (E.act_over x') Q := by
      rw [hQ, ← bcT_act, ← bcT_act]; exact h
    have h2 : pushPt (E.act (x - x')) (E.act_over (x - x')) Q = E.L.one _ := by
      letI := E.L.pointGroup (geomPoint k sk)
      rw [sub_eq_add_neg, E.act_add, h1, GenLocus10.pushPt_act_neg]
      exact mul_inv_cancel _
    have hn : (((m / ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := GenLocus10.natCast_mem hO (m / ℓ)
    have hQ' : Q = pushPt (E.act ⟨_, hn⟩) (E.act_over _) (FakeEllipticCurve.sectionAt P.P k sk) := by
      rw [CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hO.one_mem (m / ℓ) hn, hQ,
        show R₀ = nsmulPt E.L _ (m / ℓ) P.P from rfl, bcT_nsmul]
      rfl
    have hprod : ((x - x' : ↥Λ) : ℍ[ℚ, a, b]) * (((m / ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem (x - x').2 hn
    have h3 : pushPt (E.act ⟨_, hprod⟩) (E.act_over _) (FakeEllipticCurve.sectionAt P.P k sk) = E.L.one _ := by
      rw [GenLocus10.pushPt_act_comp E (x - x') ⟨_, hn⟩ hprod, ← hQ']; exact h2
    obtain ⟨y, hy⟩ := (P.annihilator k sk ⟨_, hprod⟩).1 h3
    refine ⟨y, KLAux.eq_smul_of_mul_coe _ _ ℓ m' hm'0 ?_⟩
    rw [← hm', ← hdiv, ← Submodule.coe_sub]
    exact hy

  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  haveI := E.lev_closed
  have hZ : IsClosed (Set.range E.lev.base) := E.lev.isClosedEmbedding.isClosed_range
  let Bad : ↥Λ → Set (PrimeSpectrum S) := fun x => {p | (Rx x).1.base p ∈ Set.range E.lev.base}
  have hBad : ∀ x, IsClosed (Bad x) := fun x => hZ.preimage (Rx x).1.continuous
  let Good : ↥Λ → Prop := fun x => ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - ((0 : ↥Λ) : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])
  have hGood : ∀ x, Good x → Rx x = E.L.one _ := fun x hx => by rw [hRx_congr x 0 hx, hRx_zero]
  let V : Set (PrimeSpectrum S) := ⋂ v : ZMod ℓ × ZMod ℓ, {p | Good (ρ v) ∨ p ∉ Bad (ρ v)}
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro v
    by_cases hg : Good (ρ v)
    · have : {p : PrimeSpectrum S | Good (ρ v) ∨ p ∉ Bad (ρ v)} = Set.univ := Set.eq_univ_of_forall fun p => Or.inl hg
      rw [this]; exact isOpen_univ
    · have : {p : PrimeSpectrum S | Good (ρ v) ∨ p ∉ Bad (ρ v)} = (Bad (ρ v))ᶜ := by
        ext p; simp only [Set.mem_setOf_eq, hg, false_or, Set.mem_compl_iff]
      rw [this]; exact (hBad _).isOpen_compl

  have hclosed : ∀ (k : Type) [Field k] (sk : S →+* k) (p : PrimeSpectrum S), RingHom.ker sk = p.asIdeal →
      (geomPoint k sk).base (IsLocalRing.closedPoint k) = p := by
    intro k _ sk p hp
    apply PrimeSpectrum.ext
    show Ideal.comap sk (IsLocalRing.maximalIdeal k) = p.asIdeal
    rw [← hp, show IsLocalRing.maximalIdeal k = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot]

  have hfact : ∀ (k : Type) [Field k] (sk : S →+* k) (p : PrimeSpectrum S), RingHom.ker sk = p.asIdeal → ∀ x : ↥Λ,
      (FactorsThrough E.lev (bcT (geomPoint k sk) (Rx x)) ↔ p ∈ Bad x) := by
    intro k _ sk p hp x
    have key := AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_iff_apply_closedPoint_mem_range E.lev
      (geomPoint k sk ≫ (Rx x).1)
    have hb : (geomPoint k sk ≫ (Rx x).1).base (IsLocalRing.closedPoint k) =
        (Rx x).1.base ((geomPoint k sk).base (IsLocalRing.closedPoint k)) := rfl
    rw [hb, hclosed k sk p hp] at key
    exact key

  have hgeom : ∀ p : PrimeSpectrum S, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (sk : S →+* k), RingHom.ker sk = p.asIdeal := by
    intro p
    haveI := p.isPrime
    refine ⟨AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)), inferInstance, inferInstance,
      (algebraMap (FractionRing (S ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)))).comp
        ((algebraMap (S ⧸ p.asIdeal) (FractionRing (S ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal)), ?_⟩
    ext s
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (RingHom.injective _),
      map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ p.asIdeal) (FractionRing (S ⧸ p.asIdeal))),
      Ideal.Quotient.eq_zero_iff_mem]

  suffices hUV : ∀ p : PrimeSpectrum S,
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), RingHom.ker sk = p.asIdeal →
        ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
          FactorsThrough E.lev
            (pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
          pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)) ↔ p ∈ V by
    have : {p : PrimeSpectrum S |
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), RingHom.ker sk = p.asIdeal →
        ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
          FactorsThrough E.lev
            (pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
          pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)} = V :=
      Set.ext hUV
    rw [this]; exact hV
  intro p
  constructor
  · intro hp
    refine Set.mem_iInter.2 fun v => ?_
    by_cases hg : Good (ρ v)
    · exact Or.inl hg
    · refine Or.inr fun hbad => hg ?_
      obtain ⟨k, _, _, sk, hsk⟩ := hgeom p
      have hF : FactorsThrough E.lev (bcT (geomPoint k sk) (Rx (ρ v))) := (hfact k sk p hsk (ρ v)).2 hbad
      rw [hsecRx k sk (ρ v)] at hF
      have h1 := hp k sk hsk (ρ v) (hρL v) hF
      rw [← hsecRx k sk (ρ v)] at h1

      have h2 : bcT (geomPoint k sk) (Rx (ρ v)) = bcT (geomPoint k sk) (Rx 0) := by rw [h1, hRx_zero, bcT_one]
      exact hinj_geom k sk (ρ v) 0 h2
  · intro hpV k _ _ sk hsk x hx hF
    obtain ⟨v, y, hy⟩ := hρsurj x hx
    have hxv : Rx x = Rx (ρ v) := hRx_congr x (ρ v) ⟨y, hy⟩
    have hv := (Set.mem_iInter.1 hpV) v
    rcases hv with hg | hnb
    · rw [← hsecRx k sk x, hxv, hGood _ hg, bcT_one]
    · exfalso
      apply hnb
      rw [← hsecRx k sk x, hxv] at hF
      exact (hfact k sk p hsk (ρ v)).1 hF

end TRANSVERSAL
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.GenLocus10 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.T4Aux"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel (solution)
