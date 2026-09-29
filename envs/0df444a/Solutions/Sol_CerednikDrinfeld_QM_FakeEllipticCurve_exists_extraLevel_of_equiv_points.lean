-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c27117e8-f1b4-5caf-88bf-1ab0f81c37c9

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"
universe u

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points"
namespace EnumAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"

end CerednikDrinfeld.QM.EnumAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.CerednikDrinfeld.QM.EnumAux"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points" namespace QM p2m_export "CerednikDrinfeld.QM" "mapPt mapPt_coe pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points" namespace EnumAux end CerednikDrinfeld.QM.EnumAux
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.QM" in

theorem CerednikDrinfeld.QM.EnumAux.etale_of_isReduced_of_isFinite
    {k : Type} [Field k] [IsAlgClosed k] {B : Scheme.{0}} (g : B ⟶ Spec (CommRingCat.of k))
    (hred : IsReduced B) (hfin : IsFinite g) : Etale g :=
  haveI := hred; haveI := hfin; EtaleOfReducedFinite.etale_of_isFinite_of_isReduced g

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (e : ZMod ℓ × ZMod ℓ ≃ S)
    (he : ∀ x y : ZMod ℓ × ZMod ℓ,
      ((e (x + y) : S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S)
    (hdisj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      P ∈ S → FactorsThrough E.lev P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK P ↔ P ∈ S := by
  classical
  haveI : IsProper E.f := E.bundle.proper
  letI := CerednikDrinfeld.QM.EnumAux.ptGroup E
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hfinS : S.Finite := Set.finite_coe_iff.mp (Finite.of_equiv _ e)
  have he' : ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : S) : CerednikDrinfeld.QM.EnumAux.Pt E) = (e x : CerednikDrinfeld.QM.EnumAux.Pt E) + (e y : CerednikDrinfeld.QM.EnumAux.Pt E) := he
  have hone : E.L.one (𝟙 (Spec (CommRingCat.of k))) ∈ S := by
    have h0 := CerednikDrinfeld.QM.EnumAux.equiv_map_zero e he'
    rw [← CerednikDrinfeld.QM.EnumAux.zero_def, ← h0]
    exact (e 0).2
  have hmul : ∀ x ∈ S, ∀ y ∈ S, E.L.mul (𝟙 (Spec (CommRingCat.of k))) x y ∈ S := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ : ∃ a, (e a : CerednikDrinfeld.QM.EnumAux.Pt E) = x := ⟨e.symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩
    obtain ⟨b, rfl⟩ : ∃ b, (e b : CerednikDrinfeld.QM.EnumAux.Pt E) = y := ⟨e.symm ⟨y, hy⟩, by rw [Equiv.apply_symm_apply]⟩
    rw [← he a b]
    exact (e (a + b)).2
  have hinv : ∀ x ∈ S, E.L.inv (𝟙 (Spec (CommRingCat.of k))) x ∈ S := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a, (e a : CerednikDrinfeld.QM.EnumAux.Pt E) = x := ⟨e.symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩
    have := CerednikDrinfeld.QM.EnumAux.equiv_map_neg e he' a
    show -(e a : CerednikDrinfeld.QM.EnumAux.Pt E) ∈ S
    rw [← this]
    exact (e (-a)).2
  obtain ⟨B, g, LB, i, hred, hfin, hci, hhom, eB, heB⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
      E.f E.L S hfinS hone hmul hinv
  have hget : Etale g := CerednikDrinfeld.QM.EnumAux.etale_of_isReduced_of_isFinite g hred hfin
  obtain ⟨K, -, hK⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points Λ ℓ k hℓk E B g LB i hred hfin hget hci
      hhom S eB heB e he hstab hdisj
  exact ⟨K, hK⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points (solution)
