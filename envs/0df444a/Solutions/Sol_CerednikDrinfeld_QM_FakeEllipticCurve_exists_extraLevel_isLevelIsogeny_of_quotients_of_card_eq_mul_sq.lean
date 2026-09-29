-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c41eaa69-4b53-5b77-907a-f87f4f678e1e

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_isReduced_K_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"
universe u

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero QM.FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel FakeEllipticCurve.WithExtraLevel FakeEllipticCurve.IsLevelIsogeny mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero FakeEllipticCurve.exists_extraLevel_of_equiv_points exists_comp_eq_of_forall_factorsThrough_of_isReduced FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero QM.FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel FakeEllipticCurve.WithExtraLevel FakeEllipticCurve.IsLevelIsogeny mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero FakeEllipticCurve.exists_extraLevel_of_equiv_points exists_comp_eq_of_forall_factorsThrough_of_isReduced FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero QM.FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt" namespace QM p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.ExtraLevel FakeEllipticCurve.WithExtraLevel FakeEllipticCurve.IsLevelIsogeny mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero FakeEllipticCurve.exists_extraLevel_of_equiv_points exists_comp_eq_of_forall_factorsThrough_of_isReduced FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt" namespace EnumAux end CerednikDrinfeld.QM.EnumAux
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.QM" in

theorem CerednikDrinfeld.QM.EnumAux.etale_of_isReduced_of_isFinite
    {k : Type} [Field k] [IsAlgClosed k] {B : Scheme.{0}} (g : B ⟶ Spec (CommRingCat.of k))
    (hred : IsReduced B) (hfin : IsFinite g) : Etale g :=
  haveI := hred; haveI := hfin; EtaleOfReducedFinite.etale_of_isFinite_of_isReduced g

namespace STEPU

variable {R : Type} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem map_one_of_hom {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : X ⟶ Y) (hα : α ≫ gY = gX)
    (h : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
      mapPt α hα (LX.mul t u v) = LY.mul t (mapPt α hα u) (mapPt α hα v))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α hα (LX.one t) = LY.one t := by
  have h' := h t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h'
  have := congrArg (LY.mul t (LY.inv t (mapPt α hα (LX.one t)))) h'
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

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

end STEPU
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux"

open CerednikDrinfeld.QM.EnumAux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    (H' : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hH'fin : H'.Finite)
    (hH'one : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H')
    (hH'mul : ∀ P Q, P ∈ H' → Q ∈ H' → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H')
    (hH'inv : ∀ P, P ∈ H' → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H')
    (hH'stab : ∀ (x : ↥Λ) P, P ∈ H' → pushPt (E.act x) (E.act_over x) P ∈ H')
    (hHH' : H ⊆ H') (hcard : Nat.card ↥H' = ℓ ^ 2 * Nat.card ↥H)
    (htors : ∀ P, P ∈ H' → nsmulPt E.L (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ℓ P ∈ H)
    (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A)
    (hC :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q))
    (C' : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p' : E.A ⟶ C'.A) (hp' : p' ≫ C'.f = E.f) (K' : Scheme.{0}) (κ' : K' ⟶ E.A)
    (hC' :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p' hp' (E.L.mul t P Q) = C'.L.mul t (mapPt p' hp' P) (mapPt p' hp' Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p' = p' ≫ C'.act x) ∧
      IsFinite p' ∧ Flat p' ∧ Surjective p' ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C'.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p' hp' P = R) ∧
      IsClosedImmersion κ' ∧ IsReduced K' ∧ IsFinite (κ' ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ' P ↔ P ∈ H') ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p' hp' Q = C'.L.one t ↔ FactorsThrough κ' Q))
    :
    ∃ Kx : C.ExtraLevel ℓ,
      FakeEllipticCurve.IsLevelIsogeny ℓ (⟨C, Kx⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ (AlgebraicClosure ℚ)) C' := by
  classical
  obtain ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩ := hC
  obtain ⟨p'_hom, p'_act, hp'fin, hp'flat, hp'surj, hp'onto, hκ'ci, hK'red, hκ'fin, hκ'pts, hkerp'⟩ := hC'
  have hℓP : ℓ.Prime := Fact.out
  have hO : IsOrder Λ := hΛ.1
  have hℓk : (ℓ : (AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast hℓP.ne_zero
  have hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((ℓ : ℚ) : ℍ[ℚ, a, b]) = (ℓ : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  letI iE := CerednikDrinfeld.QM.EnumAux.ptGroup E
  letI iC := CerednikDrinfeld.QM.EnumAux.ptGroup C

  let SA : AddSubgroup (Pt E) :=
    { carrier := H, add_mem' := fun {P Q} hP hQ => hHmul P Q hP hQ, zero_mem' := hHone, neg_mem' := fun {P} hP => hHinv P hP }
  let SA' : AddSubgroup (Pt E) :=
    { carrier := H', add_mem' := fun {P Q} hP hQ => hH'mul P Q hP hQ, zero_mem' := hH'one, neg_mem' := fun {P} hP => hH'inv P hP }
  have hactℓ : ∀ P : Pt E, pushPt (E.act ⟨_, hℓΛ⟩) (E.act_over _) P = ℓ • P := by
    intro P; rw [CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hO.one_mem ℓ hℓΛ, nsmulPt_eq_nsmul]
  have hact1 : E.act ⟨1, hO.one_mem⟩ = 𝟙 E.A := E.act_one hO.one_mem

  obtain ⟨φs, hφs, hpφs, φs_hom, φs_uniq, φs_lin⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E H C p hp K κ
      ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩
      H' C' p' hp' K' κ' ⟨p'_hom, p'_act, hp'fin, hp'flat, hp'surj, hp'onto, hκ'ci, hK'red, hκ'fin, hκ'pts, hkerp'⟩
      ⟨1, hO.one_mem⟩ (fun P hP => by
        rw [show pushPt (E.act ⟨1, hO.one_mem⟩) (E.act_over _) P = P from Subtype.ext (by simp [pushPt, hact1])]
        exact hHH' hP)
  rw [hact1, Category.id_comp] at hpφs
  obtain ⟨ψs, hψs, hpψs, ψs_hom, ψs_uniq, ψs_lin⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E H' C' p' hp' K' κ'
      ⟨p'_hom, p'_act, hp'fin, hp'flat, hp'surj, hp'onto, hκ'ci, hK'red, hκ'fin, hκ'pts, hkerp'⟩
      H C p hp K κ ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩
      ⟨_, hℓΛ⟩ (fun P hP => by rw [hactℓ, ← nsmulPt_eq_nsmul]; exact htors P hP)

  have hcommℓ : ∀ x : ↥Λ, E.act ⟨_, hℓΛ⟩ ≫ E.act x = E.act x ≫ E.act ⟨_, hℓΛ⟩ := by
    intro x
    have hxl : (x : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem x.2 hℓΛ
    have hlx : ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hℓΛ x.2
    have e1 := E.act_mul x ⟨_, hℓΛ⟩ hxl
    have e2 := E.act_mul ⟨_, hℓΛ⟩ x hlx
    have hc : (x : ℍ[ℚ, a, b]) * ((ℓ : ℚ) : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) :=
      (QuaternionAlgebra.coe_commutes (ℓ : ℚ) (x : ℍ[ℚ, a, b])).symm
    rw [← e1, ← e2]; congr 1; exact Subtype.ext hc
  have φs_act : ∀ x : ↥Λ, C.act x ≫ φs = φs ≫ C'.act x := fun x =>
    φs_lin x (by rw [hact1, Category.id_comp, Category.comp_id]) (fun P hP => hHstab x P hP)
  have ψs_act : ∀ x : ↥Λ, C'.act x ≫ ψs = ψs ≫ C.act x := fun x =>
    ψs_lin x (hcommℓ x) (fun P hP => hH'stab x P hP)

  have hHℓ : ∀ P, P ∈ H → pushPt (E.act ⟨_, hℓΛ⟩) (E.act_over _) P ∈ H := by
    intro P hP; rw [hactℓ]; exact SA.nsmul_mem hP ℓ
  have hH'ℓ : ∀ P, P ∈ H' → pushPt (E.act ⟨_, hℓΛ⟩) (E.act_over _) P ∈ H' := by
    intro P hP; rw [hactℓ]; exact SA'.nsmul_mem hP ℓ
  have hφψ_m : φs ≫ ψs = C.act ⟨_, hℓΛ⟩ := by
    obtain ⟨θ, hθ, -, -, θuniq, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E H C p hp K κ
        ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩
        H C p hp K κ ⟨p_hom, p_act, hpfin, hpflat, hpsurj, hponto, hκci, hKred, hκfin, hκpts, hkerp⟩ ⟨_, hℓΛ⟩ hHℓ
    have hA := θuniq (φs ≫ ψs) (by rw [Category.assoc, hψs, hφs]) (by rw [← Category.assoc, hpφs, hpψs])
    have hB := θuniq (C.act ⟨_, hℓΛ⟩) (C.act_over _) (by rw [p_act])
    rw [hA, hB]
  have hψφ_m : ψs ≫ φs = C'.act ⟨_, hℓΛ⟩ := by
    obtain ⟨θ, hθ, -, -, θuniq, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients (AlgebraicClosure ℚ) E H' C' p' hp' K' κ'
        ⟨p'_hom, p'_act, hp'fin, hp'flat, hp'surj, hp'onto, hκ'ci, hK'red, hκ'fin, hκ'pts, hkerp'⟩
        H' C' p' hp' K' κ' ⟨p'_hom, p'_act, hp'fin, hp'flat, hp'surj, hp'onto, hκ'ci, hK'red, hκ'fin, hκ'pts, hkerp'⟩ ⟨_, hℓΛ⟩ hH'ℓ
    have hA := θuniq (ψs ≫ φs) (by rw [Category.assoc, hφs, hψs]) (by rw [← Category.assoc, hpψs, Category.assoc, hpφs])
    have hB := θuniq (C'.act ⟨_, hℓΛ⟩) (C'.act_over _) (by rw [p'_act])
    rw [hA, hB]
  have hψφs : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t C.f),
      mapPt ψs hψs (mapPt φs hφs P) = nsmulPt C.L t ℓ P := by
    intro T t P
    rw [← STEPU.mapPt_comp φs hφs ψs hψs (h := by rw [Category.assoc, hψs, hφs]),
      ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C hO.one_mem ℓ hℓΛ t P]
    apply Subtype.ext; simp only [mapPt, pushPt, hφψ_m]
  have hφψs : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t C'.f),
      mapPt φs hφs (mapPt ψs hψs Q) = nsmulPt C'.L t ℓ Q := by
    intro T t Q
    rw [← STEPU.mapPt_comp ψs hψs φs hφs (h := by rw [Category.assoc, hφs, hψs]),
      ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt C' hO.one_mem ℓ hℓΛ t Q]
    apply Subtype.ext; simp only [mapPt, pushPt, hψφ_m]

  let pA : Pt E →+ Pt C :=
    { toFun := fun P => mapPt p hp P
      map_zero' := STEPU.map_one_of_hom E.L C.L p hp p_hom _
      map_add' := fun P Q => p_hom _ P Q }
  have pA_apply : ∀ P : Pt E, pA P = mapPt p hp P := fun P => rfl
  have hkerA : ∀ P : Pt E, pA P = 0 ↔ P ∈ H := by
    intro P; rw [pA_apply, ← hκpts]; exact hkerp _ P
  let T₁ : AddSubgroup (Pt C) := SA'.map pA
  have memT₁ : ∀ R : Pt C, R ∈ T₁ ↔ ∃ P ∈ H', pA P = R := fun R => AddSubgroup.mem_map

  have hT₁ℓ : ∀ R : ↥T₁, ℓ • R = 0 := by
    rintro ⟨R, hR⟩
    obtain ⟨P, hP, rfl⟩ := (memT₁ R).1 hR
    apply Subtype.ext
    show ℓ • pA P = 0
    rw [← map_nsmul, hkerA, ← nsmulPt_eq_nsmul]; exact htors P hP
  haveI : Finite ↥H' := hH'fin.to_subtype
  haveI : Finite ↥H := hHfin.to_subtype
  haveI : Finite ↥SA' := hH'fin.to_subtype
  have hcardT₁ : Nat.card ↥T₁ = ℓ ^ 2 := by
    let r : ↥SA' →+ Pt C := pA.comp SA'.subtype
    have hrange : r.range = T₁ := by
      ext R; simp only [AddMonoidHom.mem_range, memT₁]
      constructor
      · rintro ⟨⟨P, hP⟩, rfl⟩; exact ⟨P, hP, rfl⟩
      · rintro ⟨P, hP, rfl⟩; exact ⟨⟨P, hP⟩, rfl⟩
    have hker : Nat.card ↥r.ker = Nat.card ↥H := by
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, (hkerA _).1 x.2⟩, fun P => ⟨⟨P.1, hHH' P.2⟩, (hkerA _).2 P.2⟩,
        fun x => rfl, fun P => rfl⟩
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup r.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange r).toEquiv, hrange, hker,
      show Nat.card ↥SA' = Nat.card ↥H' from rfl, hcard] at h1
    have hHpos : 0 < Nat.card ↥H := Nat.card_pos_iff.2 ⟨⟨⟨_, hHone⟩⟩, inferInstance⟩
    exact (Nat.eq_of_mul_eq_mul_right hHpos h1).symm
  haveI : Finite ↥T₁ := Nat.finite_of_card_ne_zero (by rw [hcardT₁]; exact pow_ne_zero 2 hℓP.ne_zero)

  obtain ⟨e, he⟩ : ∃ e : ZMod ℓ × ZMod ℓ ≃ ↥(T₁ : Set (Pt C)),
      ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : ↥(T₁ : Set (Pt C))) : Pt C) = C.L.mul (𝟙 _) (e x) (e y) := by
    letI iM : Module (ZMod ℓ) ↥T₁ := AddCommGroup.zmodModule hT₁ℓ
    haveI hF : Module.Finite (ZMod ℓ) ↥T₁ := Module.Finite.of_finite
    haveI hFr : Module.Free (ZMod ℓ) ↥T₁ := Module.Free.of_divisionRing (ZMod ℓ) ↥T₁
    letI : Fintype ↥T₁ := Fintype.ofFinite _
    have hfr : Module.finrank (ZMod ℓ) ↥T₁ = 2 := by
      have h := @Module.card_eq_pow_finrank (ZMod ℓ) ↥T₁ _ _ iM _ _
      rw [ZMod.card, Fintype.card_eq_nat_card, hcardT₁] at h
      exact (Nat.pow_right_injective hℓP.two_le h).symm
    let B := @Module.finBasisOfFinrankEq (ZMod ℓ) ↥T₁ _ _ iM hFr _ hF 2 hfr
    let A : ↥T₁ ≃+ (Fin 2 → ZMod ℓ) := B.equivFun.toAddEquiv
    let e : ZMod ℓ × ZMod ℓ ≃ ↥T₁ := (A.toEquiv.trans (piFinTwoEquiv fun _ => ZMod ℓ)).symm
    refine ⟨e, fun x y => ?_⟩
    have hpi : ∀ u v : Fin 2 → ZMod ℓ, (piFinTwoEquiv fun _ => ZMod ℓ).symm (piFinTwoEquiv (fun _ => ZMod ℓ) u + piFinTwoEquiv (fun _ => ZMod ℓ) v) = u + v := by
      intro u v; ext i; fin_cases i <;> rfl
    have : e (x + y) = e x + e y := by
      show A.symm ((piFinTwoEquiv fun _ => ZMod ℓ).symm (x + y)) = A.symm ((piFinTwoEquiv fun _ => ZMod ℓ).symm x) + A.symm ((piFinTwoEquiv fun _ => ZMod ℓ).symm y)
      rw [← map_add]
      congr 1
      ext i; fin_cases i <;> rfl
    rw [this]; rfl
  have hT₁stab : ∀ (m : ↥Λ) (R : Pt C), R ∈ (T₁ : Set (Pt C)) → pushPt (C.act m) (C.act_over m) R ∈ (T₁ : Set (Pt C)) := by
    intro m R hR
    obtain ⟨P, hP, rfl⟩ := (memT₁ R).1 hR
    refine (memT₁ _).2 ⟨pushPt (E.act m) (E.act_over m) P, hH'stab m P hP, ?_⟩
    apply Subtype.ext
    show (P.1 ≫ E.act m) ≫ p = (P.1 ≫ p) ≫ C.act m
    rw [Category.assoc, Category.assoc, p_act]
  have hT₁disj : ∀ R : Pt C, R ∈ (T₁ : Set (Pt C)) → FactorsThrough C.lev R → R = C.L.one _ :=
    fun R _ hR => (STEPU.factorsThrough_lev_iff_eq_one C _ R).1 hR
  obtain ⟨Kx, hKx⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points Λ ℓ (AlgebraicClosure ℚ) hℓk C
    (T₁ : Set (Pt C)) e he hT₁stab hT₁disj

  haveI hKxred : IsReduced Kx.K := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero (AlgebraicClosure ℚ) C Kx hℓk
  haveI := Kx.levK_closed
  haveI := Kx.levK_finite
  set o' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C'.A := (C'.L.one (𝟙 _)).1 with ho'
  have ho'f : o' ≫ C'.f = 𝟙 _ := (C'.L.one (𝟙 _)).2
  haveI : IsProper C'.f := C'.bundle.proper
  haveI : IsClosedImmersion (o' ≫ C'.f) := by rw [ho'f]; infer_instance
  haveI : IsClosedImmersion o' := IsClosedImmersion.of_comp o' C'.f
  have hone' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))), (C'.L.one t).1 = t ≫ o' := by
    intro T t
    have hn := GoodReductionJacobian.RelativeGroupLaw.one_natural C'.L (𝟙 _) t t (Category.comp_id _)
    rw [← hn]; rfl

  obtain ⟨g₁, hg₁⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced (AlgebraicClosure ℚ)
    (Kx.levK ≫ C.f) C'.f o' (Kx.levK ≫ φs) (by rw [Category.assoc, hφs]) (by
      intro y
      let R : Pt C := ⟨y.1 ≫ Kx.levK, by rw [Category.assoc]; exact y.2⟩
      have hR : R ∈ (T₁ : Set (Pt C)) := (hKx R).1 ⟨y.1, rfl⟩
      obtain ⟨P, hP, hPR⟩ := (memT₁ R).1 hR
      have h0 : mapPt φs hφs R = 0 := by
        rw [← hPR, pA_apply, ← STEPU.mapPt_comp p hp φs hφs (h := by rw [Category.assoc, hφs, hp])]
        rw [show mapPt (p ≫ φs) _ P = mapPt p' hp' P from by apply Subtype.ext; simp only [mapPt, hpφs]]
        exact (hkerp' _ P).2 ((hκ'pts P).2 hP)
      refine ⟨𝟙 _, ?_⟩
      rw [Category.id_comp]
      show o' = y.1 ≫ (Kx.levK ≫ φs)
      rw [← Category.assoc]; exact (congrArg Subtype.val h0).symm)

  obtain ⟨hZred, hZlft, hZfin⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero (AlgebraicClosure ℚ) C C'
    φs hφs φs_hom φs_act ψs hψs ℓ hℓk hψφs hφψs
  haveI := hZred; haveI := hZlft
  obtain ⟨g₂, hg₂⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced (AlgebraicClosure ℚ)
    (pullback.fst φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1 ≫ C.f) C.f Kx.levK
    (pullback.fst φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1) rfl (by
      intro z
      let R : Pt C := ⟨z.1 ≫ pullback.fst φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1, by rw [Category.assoc]; exact z.2⟩
      have hfs : pullback.fst φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1 ≫ C.f =
          pullback.snd φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1 := by
        rw [← hφs, ← Category.assoc, pullback.condition, Category.assoc]
        show pullback.snd φs o' ≫ o' ≫ C'.f = pullback.snd φs o'
        rw [ho'f, Category.comp_id]
      have hzs : z.1 ≫ pullback.snd φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1 = 𝟙 _ := by
        rw [← hfs]; exact z.2
      have hR1 : mapPt φs hφs R = C'.L.one _ := by
        apply Subtype.ext
        rw [hone']
        show (z.1 ≫ pullback.fst φs (C'.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))).1) ≫ φs = 𝟙 _ ≫ o'
        rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
      obtain ⟨P, hP⟩ := hponto R
      have hP' : mapPt p' hp' P = C'.L.one _ := by
        rw [← hR1, ← hP, ← STEPU.mapPt_comp p hp φs hφs (h := by rw [Category.assoc, hφs, hp])]
        apply Subtype.ext; simp only [mapPt, hpφs]
      have hPH' : P ∈ H' := (hκ'pts P).1 ((hkerp' _ P).1 hP')
      have hRT : R ∈ (T₁ : Set (Pt C)) := (memT₁ R).2 ⟨P, hPH', hP⟩
      obtain ⟨c, hc⟩ := (hKx R).2 hRT
      exact ⟨c, hc⟩)

  have hkerφs : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t C.f),
      mapPt φs hφs Q = C'.L.one t ↔ FactorsThrough Kx.levK Q := by
    intro T t Q
    constructor
    · intro hQ
      have hQo : Q.1 ≫ φs = t ≫ o' := by rw [← hone']; exact congrArg Subtype.val hQ
      exact ⟨pullback.lift Q.1 t hQo ≫ g₂, by rw [Category.assoc, hg₂, pullback.lift_fst]⟩
    · rintro ⟨c, hc⟩
      apply Subtype.ext
      rw [hone']
      show Q.1 ≫ φs = t ≫ o'
      have hcg : c ≫ g₁ = t := by
        rw [← Category.comp_id (c ≫ g₁), ← ho'f, Category.assoc, ← Category.assoc g₁, hg₁, Category.assoc, hφs,
          ← Category.assoc, hc]
        exact Q.2
      rw [← hc, Category.assoc, ← hg₁, ← Category.assoc, hcg]

  have hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t C.f),
      FactorsThrough C.lev P → FactorsThrough C'.lev (mapPt φs hφs P) := by
    intro T t P hP
    rw [STEPU.factorsThrough_lev_iff_eq_one] at hP ⊢
    rw [hP]; exact STEPU.map_one_of_hom C.L C'.L φs hφs φs_hom t
  exact ⟨Kx, φs, hφs, ψs, hψs, φs_hom, ψs_hom, φs_act, ψs_act, fun hℓ' => ⟨hφψ_m, hψφ_m⟩, hkerφs, hlev⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq (solution)
