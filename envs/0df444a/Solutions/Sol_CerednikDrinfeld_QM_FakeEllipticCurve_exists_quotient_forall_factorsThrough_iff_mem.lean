-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_forall_factorsThrough_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/75052e29-14e4-50e7-9693-54825316c7f4

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"
universe u

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.exists_quotient_core_of_isAlgClosed exists_comp_eq_of_forall_factorsThrough_of_isReduced"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k]

abbrev Pt (E : FakeEllipticCurve Λ N k) : Type := SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f

noncomputable scoped instance ptAdd (E : FakeEllipticCurve Λ N k) : Add (Pt E) := ⟨fun P Q => E.L.mul (𝟙 (Spec (CommRingCat.of k))) P Q⟩
noncomputable scoped instance ptZero (E : FakeEllipticCurve Λ N k) : Zero (Pt E) := ⟨E.L.one (𝟙 (Spec (CommRingCat.of k)))⟩
noncomputable scoped instance ptNeg (E : FakeEllipticCurve Λ N k) : Neg (Pt E) := ⟨fun P => E.L.inv (𝟙 (Spec (CommRingCat.of k))) P⟩

noncomputable scoped instance ptGroup (E : FakeEllipticCurve Λ N k) : AddCommGroup (Pt E) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := E.L.mul_assoc (𝟙 (Spec (CommRingCat.of k)))
  zero_add := E.L.one_mul (𝟙 (Spec (CommRingCat.of k)))
  add_zero := E.L.mul_one (𝟙 (Spec (CommRingCat.of k)))
  neg_add_cancel := E.L.inv_mul_cancel (𝟙 (Spec (CommRingCat.of k)))
  add_comm P Q := E.comm (𝟙 (Spec (CommRingCat.of k))) P Q

section Basic

variable (E : FakeEllipticCurve Λ N k)

theorem add_def (P Q : Pt E) : P + Q = E.L.mul (𝟙 (Spec (CommRingCat.of k))) P Q := rfl

theorem zero_def : (0 : Pt E) = E.L.one (𝟙 (Spec (CommRingCat.of k))) := rfl

theorem nsmulPt_eq_nsmul (n : ℕ) (P : Pt E) : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) n P = n • P := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, add_def, ← ih]
    rfl

theorem mapPt_comp_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (φ ψ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hψ : ψ ≫ E.f = E.f) (h : (φ ≫ ψ) ≫ E.f = E.f) (P : SchemeHomOver t E.f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

theorem mapPt_id_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (h : 𝟙 E.A ≫ E.f = E.f) (P : SchemeHomOver t E.f) :
    mapPt (𝟙 E.A) h P = P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.comp_id]

noncomputable def actPt (m : ↥Λ) (P : Pt E) : Pt E := pushPt (E.act m) (E.act_over m) P

theorem actPt_def (m : ↥Λ) (P : Pt E) : actPt E m P = pushPt (E.act m) (E.act_over m) P := rfl

theorem actPt_add (m : ↥Λ) (P Q : Pt E) : actPt E m (P + Q) = actPt E m P + actPt E m Q :=
  E.act_hom m (𝟙 (Spec (CommRingCat.of k))) P Q

theorem actPt_add_left (m n : ↥Λ) (P : Pt E) : actPt E (m + n) P = actPt E m P + actPt E n P :=
  E.act_add m n (𝟙 (Spec (CommRingCat.of k))) P

theorem actPt_zero_left (P : Pt E) : actPt E 0 P = 0 := by
  have h := actPt_add_left E 0 0 P
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem actPt_neg_left (m : ↥Λ) (P : Pt E) : actPt E (-m) P = -actPt E m P := by
  have h := actPt_add_left E (-m) m P
  rw [neg_add_cancel, actPt_zero_left] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

theorem actPt_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : Pt E) : actPt E ⟨1, h1⟩ P = P := by
  have := E.act_one h1
  apply Subtype.ext
  show P.1 ≫ E.act ⟨1, h1⟩ = P.1
  rw [this, Category.comp_id]

theorem actPt_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : Pt E) :
    actPt E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P = actPt E x (actPt E y P) := by
  have := E.act_mul x y h
  apply Subtype.ext
  show P.1 ≫ E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (P.1 ≫ E.act y) ≫ E.act x
  rw [this, Category.assoc]

theorem actPt_zero (m : ↥Λ) : actPt E m 0 = 0 := by
  have h := actPt_add E m 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

noncomputable def actHom (P₀ : Pt E) : ↥Λ →+ Pt E where
  toFun m := actPt E m P₀
  map_zero' := actPt_zero_left E P₀
  map_add' m n := actPt_add_left E m n P₀

theorem actHom_apply (P₀ : Pt E) (m : ↥Λ) : actHom E P₀ m = actPt E m P₀ := rfl

noncomputable def orbit (P₀ : Pt E) : AddSubgroup (Pt E) := (actHom E P₀).range

theorem mem_orbit_iff (P₀ P : Pt E) : P ∈ orbit E P₀ ↔ ∃ m : ↥Λ, P = actPt E m P₀ := by
  rw [orbit, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

noncomputable def rho (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (n : ↥Λ) : ↥(orbit E P₀) →+ ↥(orbit E P₀) where
  toFun P := ⟨actPt E n P.1, by
    obtain ⟨m, hm⟩ := (mem_orbit_iff E P₀ P.1).1 P.2
    rw [mem_orbit_iff]
    refine ⟨⟨(n : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hΛ.mul_mem n.2 m.2⟩, ?_⟩
    rw [hm, actPt_mul]⟩
  map_zero' := by
    apply Subtype.ext
    show actPt E n (0 : Pt E) = 0
    exact actPt_zero E n
  map_add' P Q := by
    apply Subtype.ext
    show actPt E n (P.1 + Q.1) = actPt E n P.1 + actPt E n Q.1
    exact actPt_add E n P.1 Q.1

theorem rho_apply_coe (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (n : ↥Λ) (P : ↥(orbit E P₀)) :
    ((rho E hΛ P₀ n P : ↥(orbit E P₀)) : Pt E) = actPt E n P.1 := rfl

theorem rho_one (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) :
    rho E hΛ P₀ ⟨1, h⟩ = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E ⟨1, h⟩ P.1 = P.1
  exact actPt_one E h P.1

theorem rho_mul (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    rho E hΛ P₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (rho E hΛ P₀ x).comp (rho E hΛ P₀ y) := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P.1 = actPt E x (actPt E y P.1)
  exact actPt_mul E x y h P.1

theorem rho_add (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (x y : ↥Λ) :
    rho E hΛ P₀ (x + y) = rho E hΛ P₀ x + rho E hΛ P₀ y := by
  refine AddMonoidHom.ext fun P => Subtype.ext ?_
  show actPt E (x + y) P.1 = actPt E x P.1 + actPt E y P.1
  exact actPt_add_left E x y P.1

noncomputable def basePt (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) : ↥(orbit E P₀) :=
  ⟨P₀, (mem_orbit_iff E P₀ P₀).2 ⟨⟨1, hΛ.one_mem⟩, (actPt_one E hΛ.one_mem P₀).symm⟩⟩

theorem rho_basePt (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (m : ↥Λ) :
    ((rho E hΛ P₀ m (basePt E hΛ P₀) : ↥(orbit E P₀)) : Pt E) = actPt E m P₀ := rfl

theorem hgen (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) (P : ↥(orbit E P₀)) :
    ∃ m : ↥Λ, P = rho E hΛ P₀ m (basePt E hΛ P₀) := by
  obtain ⟨m, hm⟩ := (mem_orbit_iff E P₀ P.1).1 P.2
  exact ⟨m, Subtype.ext hm⟩

end Basic

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.exists_quotient_core_of_isAlgClosed exists_comp_eq_of_forall_factorsThrough_of_isReduced"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM"

section Torsion

theorem card_nsmul_eq_zero_zmod (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ∣ N) (hℓ0 : 0 < ℓ) :
    Nat.card {x : ZMod N // ℓ • x = 0} = ℓ := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  let φ : ZMod N →+ ZMod N := AddMonoidHom.mulLeft (ℓ : ZMod N)
  have hker : ∀ x : ZMod N, x ∈ φ.ker ↔ ℓ • x = 0 := by
    intro x; rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  have hrange : φ.range = AddSubgroup.zmultiples (ℓ : ZMod N) := by
    ext y
    rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨z, rfl⟩
      refine ⟨(z : ZMod N), ?_⟩
      rw [AddMonoidHom.coe_mulLeft, zsmul_eq_mul, mul_comm]
  have hcr : Nat.card φ.range = N / ℓ := by
    rw [hrange, Nat.card_zmultiples, ZMod.addOrderOf_coe ℓ hN, Nat.gcd_eq_right hℓ]
  have h1 : Nat.card (ZMod N) = Nat.card (ZMod N ⧸ φ.ker) * Nat.card φ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, hcr, Nat.card_zmod] at h1
  have h2 : Nat.card φ.ker = Nat.card {x : ZMod N // ℓ • x = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hker x)
  rw [← h2]
  have hpos : 0 < N / ℓ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hℓ) hℓ0
  have h3 : N / ℓ * Nat.card φ.ker = N / ℓ * ℓ := by rw [← h1, Nat.div_mul_cancel hℓ]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem card_nsmul_eq_zero_prod (A B : Type) [AddMonoid A] [AddMonoid B] (ℓ : ℕ) :
    Nat.card {p : A × B // ℓ • p = 0} = Nat.card {x : A // ℓ • x = 0} * Nat.card {y : B // ℓ • y = 0} := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact {
    toFun := fun p => (⟨p.1.1, by have := congrArg Prod.fst p.2; simpa using this⟩,
                       ⟨p.1.2, by have := congrArg Prod.snd p.2; simpa using this⟩)
    invFun := fun q => ⟨(q.1.1, q.2.1), by rw [Prod.smul_mk, q.1.2, q.2.2]; rfl⟩
    left_inv := fun p => rfl
    right_inv := fun q => rfl }

theorem card_nsmul_eq_zero_zmod_prod (N ℓ : ℕ) [NeZero N] (hℓ : ℓ ∣ N) (hℓ0 : 0 < ℓ) :
    Nat.card {p : ZMod N × ZMod N // ℓ • p = 0} = ℓ ^ 2 := by
  rw [card_nsmul_eq_zero_prod, card_nsmul_eq_zero_zmod N ℓ hℓ hℓ0, sq]

theorem equiv_map_zero {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) : ((e 0 : S) : H) = 0 := by
  have := he 0 0
  rw [add_zero] at this
  exact (left_eq_add.1 this)

theorem equiv_map_nsmul {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) (n : ℕ) (x : G) :
    ((e (n • x) : S) : H) = n • (e x : H) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, equiv_map_zero e he]
  | succ n ih => rw [succ_nsmul, succ_nsmul, he, ih]

theorem equiv_map_neg {G : Type} [AddGroup G] {H : Type} [AddGroup H] {S : Set H} (e : G ≃ S)
    (he : ∀ x y : G, ((e (x + y) : S) : H) = (e x : H) + (e y : H)) (x : G) :
    ((e (-x) : S) : H) = -(e x : H) := by
  have := he (-x) x
  rw [neg_add_cancel, equiv_map_zero e he] at this
  exact (neg_eq_of_add_eq_zero_left this.symm).symm

theorem ncard_eq_of_equiv_zmod_prod {H : Type} (ℓ : ℕ) [NeZero ℓ] {S : Set H} (e : ZMod ℓ × ZMod ℓ ≃ S) :
    Nat.card S = ℓ ^ 2 := by
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod, sq]

end Torsion
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"

namespace EtaleOfReducedFinite

open scoped TensorProduct

theorem formallyUnramified_of_isReduced_of_finite (K : Type u) [Field K] [PerfectField K]
    (R : Type u) [CommRing R] [Algebra K R] [Module.Finite K R] [IsReduced R] : Algebra.FormallyUnramified K R := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  haveI : ∀ I : MaximalSpectrum R, Algebra.FormallyUnramified K (R ⧸ I.asIdeal) := by
    intro I
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  haveI : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum R, R ⧸ I.asIdeal) :=
    (Algebra.FormallyUnramified.pi_iff _).mpr this
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi R).restrictScalars K).symm

theorem etale_of_isFinite_of_isReduced {K : Type u} [Field K] [PerfectField K]
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of K)) [IsFinite g] [IsReduced B] : Etale g := by
  haveI : IsAffine B := isAffine_of_isAffineHom g
  let φ : CommRingCat.of K ⟶ Γ(B, ⊤) := Spec.preimage (B.isoSpec.inv ≫ g)
  have hφ : Spec.map φ = B.isoSpec.inv ≫ g := Spec.map_preimage _
  letI : Algebra K Γ(B, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(B, ⊤) := by
    have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact h1
  haveI : Algebra.FormallyUnramified K Γ(B, ⊤) := formallyUnramified_of_isReduced_of_finite K _
  haveI hFU : FormallyUnramified (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    show Algebra.FormallyUnramified K Γ(B, ⊤)
    infer_instance
  haveI hFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp (show φ.hom.FiniteType from
      show Algebra.FiniteType K Γ(B, ⊤) from inferInstance)
  have hE : Etale (Spec.map φ) := Etale.of_formallyUnramified_of_flat _
  have : g = B.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

end EtaleOfReducedFinite
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced" namespace QM p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.exists_quotient_core_of_isAlgClosed exists_comp_eq_of_forall_factorsThrough_of_isReduced" namespace EnumAux end CerednikDrinfeld.QM.EnumAux
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.QM" in

theorem CerednikDrinfeld.QM.EnumAux.etale_of_isReduced_of_isFinite
    {k : Type} [Field k] [IsAlgClosed k] {B : Scheme.{0}} (g : B ⟶ Spec (CommRingCat.of k))
    (hred : IsReduced B) (hfin : IsFinite g) : Etale g :=
  haveI := hred; haveI := hfin; EtaleOfReducedFinite.etale_of_isFinite_of_isReduced g

namespace IMGSUB

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
private theorem _root_.IMGSUB.one (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough ι (L₀.one t))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : FactorsThrough (ι ≫ p) (L.one t) := by
  rw [factorsThrough_iff p hp ι]; exact ⟨L₀.one t, hone t, map_one L₀ L p hp hp_hom t⟩

p2m_export "IMGSUB" "one"
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

end IMGSUB
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"

namespace QBaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem one_coe_eq {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have := congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  exact this.symm

theorem inv_unique {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) (h : L.mul t y x = L.one t) :
    y = L.inv t x := by
  have := congrArg (fun z => L.mul t z (L.inv t x)) h
  rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem inv_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  apply inv_unique
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

theorem nsmulPt_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih => simp only [nsmulPt]; rw [L.mul_natural, ih]

theorem factorsThrough_lev_iff_eq_one {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type} [CommRing S]
    (X : FakeEllipticCurve Λ 1 S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t X.f) :
    FactorsThrough X.lev Q ↔ Q = X.L.one t := by
  haveI := X.lev_finite; haveI := X.lev_flat; haveI := X.lev_finitePresentation
  haveI : IsIso (X.lev ≫ X.f) := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext s; rw [X.lev_rank s]; simp
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c₁, hc₁⟩ := X.lev_one t
    have hcg : ∀ (d : T ⟶ X.C), d ≫ X.lev ≫ X.f = t → d = t ≫ inv (X.lev ≫ X.f) := by
      intro d hd; rw [← hd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have h1 : c = t ≫ inv (X.lev ≫ X.f) := hcg c (by rw [← Category.assoc, hc]; exact Q.2)
    have h2 : c₁ = t ≫ inv (X.lev ≫ X.f) := hcg c₁ (by rw [← Category.assoc, hc₁]; exact (X.L.one t).2)
    apply Subtype.ext
    rw [← hc, ← hc₁, h1, h2]
  · rintro rfl; exact X.lev_one t

end QBaux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.CerednikDrinfeld.QM.EnumAux"

open CerednikDrinfeld.QM.EnumAux QBaux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    :
    ∃ (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q) := by
  classical
  have hO : IsOrder Λ := hΛ.1
  haveI : IsProper E.f := E.bundle.proper
  letI iE := CerednikDrinfeld.QM.EnumAux.ptGroup E

  obtain ⟨B, g, LB, i, hred, hfin, hci, hhom, eB, heB⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
      E.f E.L H hHfin hHone (fun x hx y hy => hHmul x y hx hy) hHinv
  have hget : Etale g := CerednikDrinfeld.QM.EnumAux.etale_of_isReduced_of_isFinite g hred hfin
  haveI := hred; haveI := hfin; haveI := hget; haveI := hci
  have hi : i.1 ≫ E.f = g := i.2
  have hpts : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
      (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) g, NeronModelInfra.schemeHomOverComp y i = z) ↔ z ∈ H := by
    intro z
    constructor
    · rintro ⟨y, rfl⟩; rw [← heB]; exact (eB y).2
    · intro hz; exact ⟨eB.symm ⟨z, hz⟩, by rw [← heB, Equiv.apply_symm_apply]⟩
  set e₀ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ E.A := (E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1 with he₀
  have he₀f : e₀ ≫ E.f = 𝟙 _ := (E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).2
  haveI : IsClosedImmersion (e₀ ≫ E.f) := by rw [he₀f]; infer_instance
  haveI : IsClosedImmersion e₀ := IsClosedImmersion.of_comp e₀ E.f

  have hone_i : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      NeronModelInfra.schemeHomOverComp (LB.one t) i = E.L.one t := by
    intro T t
    apply QBaux.eq_one_of_mul_self
    rw [← hhom, LB.one_mul]
  have hinv_i : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (z : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.inv t z) i = E.L.inv t (NeronModelInfra.schemeHomOverComp z i) := by
    intro T t z
    apply QBaux.inv_unique
    rw [← hhom, LB.inv_mul_cancel, hone_i]

  have hFT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P ↔ ∃ z : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp z i = P := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀, ?_⟩, Subtype.ext hP₀⟩
      rw [← hi, ← Category.assoc, hP₀]; exact P.2
    · rintro ⟨z, hz⟩; exact ⟨z.1, congrArg Subtype.val hz⟩
  have hBpt : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) g, NeronModelInfra.schemeHomOverComp y i ∈ H :=
    fun y => (hpts _).1 ⟨y, rfl⟩

  let SA : AddSubgroup (Pt E) :=
    { carrier := H
      add_mem' := fun {P Q} hP hQ => hHmul P Q hP hQ
      zero_mem' := hHone
      neg_mem' := fun {P} hP => hHinv P hP }
  set ℓ : ℕ := Nat.card ↥H with hℓdef
  haveI : Finite ↥H := hHfin.to_subtype
  have hℓpos : 0 < ℓ := by
    rw [hℓdef]; exact Nat.card_pos_iff.2 ⟨⟨⟨_, hHone⟩⟩, inferInstance⟩
  have hℓk : (ℓ : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  have hS_tors : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, P ∈ H →
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ℓ P = E.L.one _ := by
    intro P hP
    rw [nsmulPt_eq_nsmul]
    have hx : addOrderOf (⟨P, hP⟩ : ↥SA) ∣ ℓ := by
      rw [hℓdef, show Nat.card ↥H = Nat.card ↥SA from rfl]; exact addOrderOf_dvd_natCard _
    have := addOrderOf_dvd_iff_nsmul_eq_zero.1 hx
    exact congrArg Subtype.val this

  have hDfac : ∃ g₀ : B ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)), g₀ ≫ e₀ = (nsmulPt E.L g ℓ i).1 := by
    refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced (AlgebraicClosure ℚ) g E.f e₀ (nsmulPt E.L g ℓ i).1
      (nsmulPt E.L g ℓ i).2 ?_
    intro z
    have hnat : mapPt (nsmulPt E.L g ℓ i).1 (nsmulPt E.L g ℓ i).2 z =
        nsmulPt E.L (𝟙 _) ℓ (NeronModelInfra.schemeHomOverComp z i) := by
      have := nsmulPt_natural E.L g (𝟙 _) z.1 z.2 ℓ i
      exact this
    refine ⟨𝟙 _, ?_⟩
    rw [Category.id_comp, he₀, congrArg Subtype.val hnat, hS_tors _ (hBpt z)]
  have hD : nsmulPt E.L g ℓ i = E.L.one g := by
    obtain ⟨g₀, hg₀⟩ := hDfac
    have hg : g₀ = g := by
      rw [← Category.comp_id g₀, ← he₀f, ← Category.assoc, hg₀]; exact (nsmulPt E.L g ℓ i).2
    apply Subtype.ext
    rw [← hg₀, hg, one_coe_eq E.L g]

  have hact : ∀ m : ↥Λ, ∃ am : B ⟶ B, am ≫ i.1 = i.1 ≫ E.act m := by
    intro m
    refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced (AlgebraicClosure ℚ) g E.f i.1 (i.1 ≫ E.act m)
      (by rw [Category.assoc, E.act_over, hi]) ?_
    intro z
    have hmem : pushPt (E.act m) (E.act_over m) (NeronModelInfra.schemeHomOverComp z i) ∈ H := hHstab m _ (hBpt z)
    obtain ⟨y, hy⟩ := (hpts _).2 hmem
    refine ⟨y.1, ?_⟩
    have := congrArg Subtype.val hy
    simp only [mapPt_coe] at this ⊢
    rw [← Category.assoc]
    exact this

  have hκsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 Q → FactorsThrough i.1 (E.L.mul t P Q) ∧ FactorsThrough i.1 (E.L.inv t P) := by
    intro T t P Q hP hQ
    obtain ⟨zP, rfl⟩ := (hFT t P).1 hP
    obtain ⟨zQ, rfl⟩ := (hFT t Q).1 hQ
    exact ⟨(hFT t _).2 ⟨LB.mul t zP zQ, hhom t zP zQ⟩, (hFT t _).2 ⟨LB.inv t zP, hinv_i t zP⟩⟩
  have hκone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))), FactorsThrough i.1 (E.L.one t) :=
    fun t => (hFT t _).2 ⟨LB.one t, hone_i t⟩
  have hκtors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → nsmulPt E.L t ℓ P = E.L.one t := by
    intro T t P hP
    obtain ⟨zP, rfl⟩ := (hFT t P).1 hP
    have := nsmulPt_natural E.L g t zP.1 zP.2 ℓ i
    rw [hD, E.L.one_natural] at this
    exact this.symm
  have hκstab : ∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 (pushPt (E.act m) (E.act_over m) P) := by
    intro m T t P hP
    obtain ⟨zP, rfl⟩ := (hFT t P).1 hP
    obtain ⟨am, ham⟩ := hact m
    exact ⟨zP.1 ≫ am, by simp only [mapPt_coe, Category.assoc, ham]; rfl⟩
  have hfin' : IsFinite (i.1 ≫ E.f) := by rw [hi]; exact hfin
  have hflat' : Flat (i.1 ≫ E.f) := by rw [hi]; infer_instance
  have hlfp' : LocallyOfFinitePresentation (i.1 ≫ E.f) := by rw [hi]; infer_instance

  obtain ⟨A, f, L, act, hactover, p, hp, ψ, hψ, hcomm, hbundle, hdim, hact_hom, hact_one, hact_mul, hact_add, htrace,
      hp_hom, hequiv, hfinp, hflatp, hlfpp, hsurjp, hEtp, hrank, hker, hψ_hom, hψ_lin, hψp, hpψ, huniv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed (AlgebraicClosure ℚ) E hO ℓ hℓk B i.1 hci
      hfin' hflat' hlfp' hκone hκsub hκstab hκtors
  haveI := E.lev_closed
  haveI := hfinp
  have hdisj : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → mapPt p hp P = L.one t → P = E.L.one t :=
    fun t P hC _ => (QBaux.factorsThrough_lev_iff_eq_one E t P).1 hC
  haveI : IsFinite (E.lev ≫ p) := inferInstance
  have hlevf : (E.lev ≫ p) ≫ f = E.lev ≫ E.f := by rw [Category.assoc, hp]
  let C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ) :=
    { A := A
      f := f
      L := L
      comm := hcomm
      bundle := hbundle
      dim_fibre := hdim
      act := act
      act_over := hactover
      act_hom := hact_hom
      act_one := hact_one
      act_mul := hact_mul
      act_add := hact_add
      act_trace := htrace
      C := E.C
      lev := E.lev ≫ p
      lev_closed := IMGSUB.isClosedImmersion E.L L p hp hp_hom E.lev E.lev_sub hdisj
      lev_sub := fun t P Q hP hQ => IMGSUB.sub E.L L p hp hp_hom E.lev E.lev_sub t P Q hP hQ
      lev_one := fun t => IMGSUB.one E.L L p hp hp_hom E.lev E.lev_one t
      lev_torsion := fun t P hP => IMGSUB.torsion E.L L p hp hp_hom E.lev 1 E.lev_torsion t P hP
      lev_stable := fun x _ t P hP =>
        IMGSUB.stable p hp E.lev (E.act x) (E.act_over x) (act x) (hactover x) (hequiv x).symm (E.lev_stable x) t P hP
      lev_finite := by rw [hlevf]; exact E.lev_finite
      lev_flat := by rw [hlevf]; exact E.lev_flat
      lev_finitePresentation := by rw [hlevf]; exact E.lev_finitePresentation
      lev_rank := fun s => by rw [hlevf]; exact E.lev_rank s
      lev_fibre := fun k' _ _ sk hN => by
        obtain ⟨e₁, he₁⟩ := E.lev_fibre k' sk hN
        obtain ⟨e₂, he₂⟩ := IMGSUB.exists_equiv E.L L p hp hp_hom E.lev E.lev_sub hdisj (geomPoint k' sk)
        refine ⟨e₁.trans e₂, fun x y => ?_⟩
        simp only [Equiv.trans_apply]
        rw [he₂, he₂, he₂, he₁, hp_hom] }

  have honto : ∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f,
      ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R := by
    intro R
    haveI : Smooth C.f := C.bundle.smooth
    haveI : ConnectedSpace C.A := by
      rw [connectedSpace_iff_univ]
      let s₀ : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))) := ⟨⊥, Ideal.isPrime_bot⟩
      have hsub : ∀ s : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))), s = s₀ := fun s =>
        PrimeSpectrum.ext (Ideal.eq_bot_of_prime s.asIdeal)
      have hs : C.f.base ⁻¹' {s₀} = Set.univ := Set.eq_univ_of_forall fun x => hsub _
      rw [← hs]; exact C.bundle.connectedFibres s₀
    obtain ⟨R₀, hR₀⟩ := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
      C.L C.comm ℓ (isUnit_iff_ne_zero.mpr hℓk) R
    refine ⟨mapPt ψ hψ R₀, ?_⟩
    rw [hpψ, ← hR₀]
    clear hR₀
    induction ℓ with
    | zero => rfl
    | succ j ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl
  refine ⟨C, p, hp, B, i.1, hp_hom, hequiv, hfinp, hflatp, hsurjp, honto, hci, hred, hfin', ?_, hker⟩
  intro P; exact (hFT _ P).trans (hpts P)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem (solution)
