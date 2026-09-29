-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/50e7e3ab-5e1c-5510-ad7e-42a75e4cfa14

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

noncomputable section

namespace P2mQuatLabel
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

@[scoped ext] structure Pt (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : Type where

  val : SchemeHomOver t f

namespace Pt

variable (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))

scoped instance : Zero (Pt L t) := ⟨⟨L.one t⟩⟩

scoped instance : Add (Pt L t) := ⟨fun P Q => ⟨L.mul t P.val Q.val⟩⟩

scoped instance : Neg (Pt L t) := ⟨fun P => ⟨L.inv t P.val⟩⟩

scoped instance [Fact L.IsCommutative] : AddCommGroup (Pt L t) where
  add_assoc P Q S := Pt.ext (L.mul_assoc t _ _ _)
  zero_add P := Pt.ext (L.one_mul t _)
  add_zero P := Pt.ext (L.mul_one t _)
  neg_add_cancel P := Pt.ext (L.inv_mul_cancel t _)
  add_comm P Q := Pt.ext (RelativeGroupLaw.IsCommutative.mul_comm (Fact.out (p := L.IsCommutative)) t P.val Q.val)
  nsmul := nsmulRec
  zsmul := zsmulRec

variable {L t}

@[scoped simp] theorem val_add (P Q : Pt L t) : (P + Q).val = L.mul t P.val Q.val := rfl

@[scoped simp] theorem val_zero : (0 : Pt L t).val = L.one t := rfl

end Pt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt"

theorem pushPt_natural {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A' ⟶ A') (hφ : φ ≫ f' = f')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (pushPt φ hφ P) =
      pushPt φ hφ (GoodReductionJacobian.schemeHomOverComp ψ hψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

section Entries

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative]
  {c d : ℚ} {O : Submodule ℤ ℍ[ℚ, c, d]}
  (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
  (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
  {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}

def E (u : ℍ[ℚ, c, d]) (hu : u ∈ O) : Pt L t →+ Pt L t :=
  AddMonoidHom.mk' (fun P => ⟨pushPt (ε ⟨u, hu⟩) (hε _) P.val⟩) fun P Q => Pt.ext (hε_hom ⟨u, hu⟩ t P.val Q.val)

@[scoped simp] theorem val_E (u : ℍ[ℚ, c, d]) (hu : u ∈ O) (P : Pt L t) :
    (E ε hε hε_hom u hu P).val = pushPt (ε ⟨u, hu⟩) (hε _) P.val := rfl

theorem E_congr {u v : ℍ[ℚ, c, d]} (huv : u = v) (hu : u ∈ O) (hv : v ∈ O) :
    (E ε hε hε_hom u hu : Pt L t →+ Pt L t) = E ε hε hε_hom v hv := by
  subst huv; rfl

theorem E_add
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (u v : ℍ[ℚ, c, d]) (hu : u ∈ O) (hv : v ∈ O) (h : u + v ∈ O) :
    (E ε hε hε_hom (u + v) h : Pt L t →+ Pt L t) = E ε hε hε_hom u hu + E ε hε hε_hom v hv := by
  refine AddMonoidHom.ext fun P => Pt.ext ?_
  simp only [val_E, AddMonoidHom.add_apply, Pt.val_add]
  have key := hε_add ⟨u, hu⟩ ⟨v, hv⟩ t P.val
  have hsub : ((⟨u, hu⟩ : ↥O) + ⟨v, hv⟩) = ⟨u + v, h⟩ := Subtype.ext rfl
  rw [hsub] at key
  exact key

theorem E_mul
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (u v : ℍ[ℚ, c, d]) (hu : u ∈ O) (hv : v ∈ O) (h : u * v ∈ O) :
    (E ε hε hε_hom (u * v) h : Pt L t →+ Pt L t) = (E ε hε hε_hom u hu).comp (E ε hε hε_hom v hv) := by
  refine AddMonoidHom.ext fun P => Pt.ext (Subtype.ext ?_)
  simp only [val_E, AddMonoidHom.comp_apply]
  simp only [mapPt_coe]
  rw [hε_mul ⟨u, hu⟩ ⟨v, hv⟩ h, Category.assoc]

theorem E_one (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A) (h : (1 : ℍ[ℚ, c, d]) ∈ O) :
    (E ε hε hε_hom 1 h : Pt L t →+ Pt L t) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun P => Pt.ext (Subtype.ext ?_)
  simp only [val_E, AddMonoidHom.id_apply]
  simp only [mapPt_coe, hε_one h, Category.comp_id]

theorem E_zero
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (h : (0 : ℍ[ℚ, c, d]) ∈ O) :
    (E ε hε hε_hom 0 h : Pt L t →+ Pt L t) = 0 := by
  have h2 := E_add ε hε hε_hom (t := t) hε_add 0 0 h h (by rw [add_zero]; exact h)
  have h3 : (E ε hε hε_hom (0 + 0) (by rw [add_zero]; exact h) : Pt L t →+ Pt L t) = E ε hε hε_hom 0 h :=
    E_congr ε hε hε_hom (add_zero 0) _ _
  rw [h3] at h2
  have h4 : (E ε hε hε_hom 0 h : Pt L t →+ Pt L t) + E ε hε hε_hom 0 h = 0 + E ε hε hε_hom 0 h := by
    rw [zero_add]; exact h2.symm
  exact add_right_cancel h4

end Entries
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt"

section Scalars

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative] {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}

theorem mk_nsmulPt (m : ℕ) (Q : SchemeHomOver t f) : (⟨nsmulPt L t m Q⟩ : Pt L t) = m • (⟨Q⟩ : Pt L t) := by
  induction m with
  | zero => rw [zero_smul]; rfl
  | succ m ih =>
    rw [succ_nsmul, ← ih]
    rfl

variable {c d : ℚ} {O : Submodule ℤ ℍ[ℚ, c, d]}
  (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
  (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
  (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
  (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
    pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
  (hO1 : (1 : ℍ[ℚ, c, d]) ∈ O)

include hε_one hε_add hO1 in

theorem E_natCast_smul_one (m : ℕ) (h : ((m : ℚ) • (1 : ℍ[ℚ, c, d])) ∈ O) :
    (E ε hε hε_hom ((m : ℚ) • (1 : ℍ[ℚ, c, d])) h : Pt L t →+ Pt L t) = m • AddMonoidHom.id (Pt L t) := by
  induction m with
  | zero =>
    rw [zero_smul, E_congr ε hε hε_hom (by rw [Nat.cast_zero, zero_smul]) _ O.zero_mem, E_zero ε hε hε_hom hε_add]
  | succ m ih =>
    have hm : ((m : ℚ) • (1 : ℍ[ℚ, c, d])) ∈ O := by
      have := O.smul_mem (m : ℤ) hO1
      rwa [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast] at this
    rw [E_congr ε hε hε_hom (by rw [Nat.cast_succ, add_smul, one_smul]) _ (O.add_mem hm hO1),
      E_add ε hε hε_hom hε_add _ _ hm hO1, ih hm, E_one ε hε hε_hom hε_one, succ_nsmul]

include hε_one hε_add hO1 in

theorem E_intCast_smul_one (c₀ : ℤ) (h : ((c₀ : ℚ) • (1 : ℍ[ℚ, c, d])) ∈ O) :
    (E ε hε hε_hom ((c₀ : ℚ) • (1 : ℍ[ℚ, c, d])) h : Pt L t →+ Pt L t) = c₀ • AddMonoidHom.id (Pt L t) := by
  have hnat : ∀ m : ℕ, ((m : ℚ) • (1 : ℍ[ℚ, c, d])) ∈ O := fun m => by
    have := O.smul_mem (m : ℤ) hO1
    rwa [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast] at this
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c₀
  · rw [E_congr ε hε hε_hom (by rw [Int.cast_natCast]) _ (hnat m), E_natCast_smul_one ε hε hε_hom hε_one hε_add hO1,
      natCast_zsmul]
  · have hneg : (((-(m : ℤ) : ℤ) : ℚ) • (1 : ℍ[ℚ, c, d])) = -(((m : ℚ)) • (1 : ℍ[ℚ, c, d])) := by
      rw [Int.cast_neg, Int.cast_natCast, neg_smul]
    have hsum := E_add ε hε hε_hom (t := t) hε_add _ _ h (hnat m) (by rw [hneg, neg_add_cancel]; exact O.zero_mem)
    rw [E_congr ε hε hε_hom (by rw [hneg, neg_add_cancel]) _ O.zero_mem, E_zero ε hε hε_hom hε_add,
      E_natCast_smul_one ε hε hε_hom hε_one hε_add hO1] at hsum
    rw [neg_smul, natCast_zsmul]
    exact (neg_eq_of_add_eq_zero_left hsum.symm).symm

include hε_add in

theorem E_sub (u v : ℍ[ℚ, c, d]) (hu : u ∈ O) (hv : v ∈ O) (h : u - v ∈ O) :
    (E ε hε hε_hom (u - v) h : Pt L t →+ Pt L t) = E ε hε hε_hom u hu - E ε hε hε_hom v hv := by
  have hsum := E_add ε hε hε_hom (t := t) hε_add _ _ h hv (by rw [sub_add_cancel]; exact hu)
  rw [E_congr ε hε hε_hom (sub_add_cancel u v) _ hu] at hsum
  rw [hsum, add_sub_cancel_right]

end Scalars
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt"

section Single

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative]
  (φ : A ⟶ A) (hφ : φ ≫ f = f)
  (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
  {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}

def F : Pt L t →+ Pt L t := AddMonoidHom.mk' (fun P => ⟨pushPt φ hφ P.val⟩) fun P Q => Pt.ext (hhom t P.val Q.val)

@[scoped simp] theorem val_F (P : Pt L t) : (F φ hφ hhom P).val = pushPt φ hφ P.val := rfl

end Single
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt"

theorem nsmul_eq_self_of_modEq {M : Type*} [AddCommGroup M] {n K r : ℕ} (hK : r ^ K ≡ 1 [MOD n]) {p : M}
    (hp : n • p = 0) : (r ^ K) • p = p := by
  have hd : (n : ℤ) ∣ (1 : ℤ) - (r ^ K : ℕ) := (Nat.modEq_iff_dvd.mp hK)
  obtain ⟨q, hq⟩ := hd
  have hrk : ((r ^ K : ℕ) : ℤ) = 1 - (n : ℤ) * q := by omega
  have hp' : (n : ℤ) • p = 0 := by rw [natCast_zsmul]; exact hp
  calc (r ^ K) • p = ((r ^ K : ℕ) : ℤ) • p := (natCast_zsmul _ _).symm
    _ = (1 - (n : ℤ) * q) • p := by rw [hrk]
    _ = p - q • ((n : ℤ) • p) := by rw [sub_smul, one_smul, mul_comm, ← smul_smul]
    _ = p := by rw [hp', smul_zero, sub_zero]

theorem nsmul_map_eq_zero {M : Type*} [AddCommGroup M] (F : M →+ M) {n : ℕ} {p : M} (hp : n • p = 0) :
    n • F p = 0 := by
  rw [← map_nsmul, hp, map_zero]

end P2mQuatLabel
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel.Pt P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one.P2mQuatLabel"

open P2mQuatLabel in

theorem solution
    {r N n : ℕ} (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (A₀ : FakeEllipticCurve Λ N k₀) (P₀ : A₀.FullLevel n)

    {a₁ b₁ : ℚ} (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (ε : ↥R → (A₀.A ⟶ A₀.A)) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f)
    (hε_hom : ∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      pushPt (ε x) (hε x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_lin : ∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ ε x = ε x ≫ A₀.act m)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (u : (ℍ[ℚ, a₁, b₁])ˣ)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (K : ↥Γt → ℕ) (x : ↥Γt → ↥R)
    (hx : ∀ γ : ↥Γt, (x γ : ℍ[ℚ, a₁, b₁]) =
      ((r ^ K γ : ℕ) : ℚ) • ((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
    (he_eq : ∀ γ : ↥Γt, e γ = ε (x γ))
    (hK : ∀ γ : ↥Γt, r ^ K γ ≡ 1 [MOD n]) :
    ∃ lab : ↥Γt → ↥Λ,
      (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
      (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) := by
  classical
  haveI : Fact A₀.L.IsCommutative := ⟨A₀.comm⟩

  have hg : geomPoint k₀ (RingHom.id k₀) = 𝟙 (Spec (CommRingCat.of k₀)) := by
    show Spec.map (CommRingCat.ofHom (RingHom.id k₀)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  set g := geomPoint k₀ (RingHom.id k₀) with hg_def

  let toG : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f → SchemeHomOver g A₀.f :=
    fun Q => schemeHomOverComp g (Category.comp_id _) Q
  have toG_inj : ∀ Q Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f, toG Q = toG Q' → Q = Q' := by
    intro Q Q' h
    have h1 : g ≫ Q.1 = g ≫ Q'.1 := congrArg Subtype.val h
    rw [hg, Category.id_comp, Category.id_comp] at h1
    exact Subtype.ext h1
  have toG_P : toG P₀.P = FakeEllipticCurve.sectionAt P₀.P k₀ (RingHom.id k₀) := rfl
  have toG_push : ∀ (ψ : A₀.A ⟶ A₀.A) (hψ : ψ ≫ A₀.f = A₀.f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f),
      toG (pushPt ψ hψ Q) = pushPt ψ hψ (toG Q) := fun ψ hψ Q => pushPt_natural ψ hψ g _ Q
  have toG_mul : ∀ Q Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      toG (A₀.L.mul _ Q Q') = A₀.L.mul g (toG Q) (toG Q') := fun Q Q' => A₀.L.mul_natural _ _ g _ Q Q'
  have toG_one : toG (A₀.L.one _) = A₀.L.one g := A₀.L.one_natural _ _ g _
  have toG_nsmul : ∀ (m : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f),
      toG (nsmulPt A₀.L _ m Q) = nsmulPt A₀.L g m (toG Q) := by
    intro m Q
    induction m with
    | zero => exact toG_one
    | succ m ih =>
      show toG (A₀.L.mul _ (nsmulPt A₀.L _ m Q) Q) = A₀.L.mul g (nsmulPt A₀.L g m (toG Q)) (toG Q)
      rw [toG_mul, ih]

  let p : Pt A₀.L g := ⟨toG P₀.P⟩
  have hp : n • p = 0 := by
    apply Pt.ext
    show (n • p).val = A₀.L.one g
    rw [← mk_nsmulPt]
    show nsmulPt A₀.L g n (toG P₀.P) = A₀.L.one g
    rw [← toG_nsmul, P₀.torsion, toG_one]

  have hee_hom : ∀ (γ : ↥Γt) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      pushPt (e γ) (he γ) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (e γ) (he γ) P) (pushPt (e γ) (he γ) Q) := by
    intro γ T t P Q
    have := hε_hom (x γ) t P Q
    have key : ∀ Q' : SchemeHomOver t A₀.f, pushPt (e γ) (he γ) Q' = pushPt (ε (x γ)) (hε _) Q' := fun Q' =>
      Subtype.ext (by simp only [mapPt_coe, he_eq γ])
    rw [key, key, key]; exact this
  let Eact : ↥Λ → (Pt A₀.L g →+ Pt A₀.L g) := fun m => E A₀.act A₀.act_over A₀.act_hom (m : ℍ[ℚ, a, b]) m.2
  let Eε : ↥R → (Pt A₀.L g →+ Pt A₀.L g) := fun y => E ε hε hε_hom (y : ℍ[ℚ, a₁, b₁]) y.2
  let Fγ : ↥Γt → (Pt A₀.L g →+ Pt A₀.L g) := fun γ => F (e γ) (he γ) (fun t P Q => hee_hom γ t P Q)
  have Fγ_eq : ∀ γ, Fγ γ = Eε (x γ) := fun γ => by
    refine AddMonoidHom.ext fun q => Pt.ext (Subtype.ext ?_)
    simp only [Fγ, Eε, val_F, val_E, mapPt_coe]
    rw [he_eq γ]
  have Fγ_Eact : ∀ γ (m : ↥Λ) (q : Pt A₀.L g), Fγ γ (Eact m q) = Eact m (Fγ γ q) := fun γ m q => by
    refine Pt.ext (Subtype.ext ?_)
    simp only [Fγ, Eact, val_F, val_E, mapPt_coe, Category.assoc]
    rw [he_eq γ, hε_lin (x γ) m]

  have hFp : ∀ γ, n • Fγ γ p = 0 := fun γ => nsmul_map_eq_zero _ hp

  have annih : ∀ (u : ℍ[ℚ, a, b]) (hu : u ∈ Λ), E A₀.act A₀.act_over A₀.act_hom u hu p = 0 →
      ∃ y : ↥Λ, u = (n : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro u hu h0
    have := congrArg Pt.val h0
    exact (P₀.annihilator k₀ (RingHom.id k₀) ⟨u, hu⟩).mp this

  have hgen : ∀ γ : ↥Γt, ∃ m : ↥Λ, Eact m p = Fγ γ p := by
    intro γ
    have htor : nsmulPt A₀.L g n (Fγ γ p).val = A₀.L.one g := by
      have := congrArg Pt.val (hFp γ)
      rwa [← mk_nsmulPt] at this
    obtain ⟨m, hm⟩ := P₀.generates k₀ (RingHom.id k₀) (Fγ γ p).val htor
    exact ⟨m, Pt.ext hm⟩
  choose lab hlab using hgen
  refine ⟨lab, ?_, ?_, ?_⟩
  ·
    intro γ
    apply toG_inj
    have := congrArg Pt.val (hlab γ)

    simp only [Eact, Fγ, val_E, val_F] at this
    rw [toG_push, toG_push]
    exact this.symm
  ·
    intro γ γ'

    have hcoc : ((r ^ K (γ * γ') : ℕ) : ℚ) • ((x γ : ℍ[ℚ, a₁, b₁]) * (x γ' : ℍ[ℚ, a₁, b₁])) =
        ((r ^ (K γ + K γ') : ℕ) : ℚ) • (x (γ * γ') : ℍ[ℚ, a₁, b₁]) := by
      rw [hx γ, hx γ', hx (γ * γ'), pow_add]
      push_cast
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      have hu : ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (u : ℍ[ℚ, a₁, b₁]) *
          (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((γ' : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (u : ℍ[ℚ, a₁, b₁])) =
          ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((γ' : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * (u : ℍ[ℚ, a₁, b₁]) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [hu]
      congr 1
      ring

    have hr1 : ∀ (a₀ : ℕ), (((r ^ a₀ : ℕ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) ∈ R := fun a₀ => by
      have := R.smul_mem ((r ^ a₀ : ℕ) : ℤ) hR.one_mem
      rwa [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast] at this
    have hz1 : (((r ^ K (γ * γ') : ℕ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) * ((x γ : ℍ[ℚ, a₁, b₁]) * (x γ' : ℍ[ℚ, a₁, b₁])) ∈ R := hR.mul_mem (hr1 _) (hR.mul_mem (x γ).2 (x γ').2)
    have hz2 : (((r ^ (K γ + K γ') : ℕ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) * (x (γ * γ') : ℍ[ℚ, a₁, b₁]) ∈ R := hR.mul_mem (hr1 _) (x (γ * γ')).2
    have hzz : (((r ^ K (γ * γ') : ℕ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) * ((x γ : ℍ[ℚ, a₁, b₁]) * (x γ' : ℍ[ℚ, a₁, b₁])) =
        (((r ^ (K γ + K γ') : ℕ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) * (x (γ * γ') : ℍ[ℚ, a₁, b₁]) := by
      rw [smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, hcoc]
    have hop : ((r ^ K (γ * γ') : ℕ) • ((Fγ γ).comp (Fγ γ')) : Pt A₀.L g →+ Pt A₀.L g) =
        (r ^ (K γ + K γ')) • Fγ (γ * γ') := by
      have l1 := E_mul ε hε hε_hom (t := g) hε_mul _ _ (hr1 (K (γ * γ'))) (hR.mul_mem (x γ).2 (x γ').2) hz1
      have l2 := E_mul ε hε hε_hom (t := g) hε_mul _ _ (hr1 (K γ + K γ')) (x (γ * γ')).2 hz2
      rw [E_congr ε hε hε_hom hzz hz1 hz2] at l1
      rw [l1, E_natCast_smul_one ε hε hε_hom hε_one hε_add hR.one_mem,
        E_natCast_smul_one ε hε hε_hom hε_one hε_add hR.one_mem,
        E_mul ε hε hε_hom hε_mul _ _ (x γ).2 (x γ').2] at l2

      rw [Fγ_eq, Fγ_eq, Fγ_eq]
      refine AddMonoidHom.ext fun q => ?_
      have := congrArg (fun φ : Pt A₀.L g →+ Pt A₀.L g => φ q) l2
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at this ⊢
      exact this
    have hcomp : Fγ (γ * γ') p = Fγ γ (Fγ γ' p) := by
      have h1 : (r ^ K (γ * γ')) • Fγ γ (Fγ γ' p) = (r ^ (K γ + K γ')) • Fγ (γ * γ') p := by
        have := congrArg (fun φ : Pt A₀.L g →+ Pt A₀.L g => φ p) hop
        simpa only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply] using this
      rw [nsmul_eq_self_of_modEq (hK (γ * γ')) (nsmul_map_eq_zero _ (hFp γ')), pow_add, mul_comm, ← smul_smul,
        nsmul_eq_self_of_modEq (hK γ) (hFp (γ * γ')), nsmul_eq_self_of_modEq (hK γ') (hFp (γ * γ'))] at h1
      exact h1.symm

    have hprod : (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem (lab γ').2 (lab γ).2
    have hdiff : (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) ∈ Λ :=
      Λ.sub_mem (lab (γ * γ')).2 hprod
    have hkill : E A₀.act A₀.act_over A₀.act_hom _ hdiff p = 0 := by
      rw [E_sub A₀.act A₀.act_over A₀.act_hom A₀.act_add _ _ (lab (γ * γ')).2 hprod hdiff,
        E_mul A₀.act A₀.act_over A₀.act_hom A₀.act_mul _ _ (lab γ').2 (lab γ).2 hprod,
        AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
      change Eact (lab (γ * γ')) p - Eact (lab γ') (Eact (lab γ) p) = 0
      rw [hlab, hlab γ, ← Fγ_Eact, hlab γ', hcomp, sub_self]
    exact annih _ hdiff hkill
  ·
    intro γ c₀ hγ
    have hc1 : ((c₀ : ℚ) • (1 : ℍ[ℚ, a, b])) ∈ Λ := by
      have := Λ.smul_mem c₀ hΛ.one_mem
      rwa [← Int.cast_smul_eq_zsmul ℚ] at this
    have hconj : (((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u) : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c₀ : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) := by
      rw [Units.val_mul, Units.val_mul, hγ, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]
    have hxc : (x γ : ℍ[ℚ, a₁, b₁]) = ((((r ^ K γ : ℕ) : ℤ) * c₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) := by
      rw [hx γ, hconj, smul_smul]
      push_cast
      ring_nf
    have hxmem : (((((r ^ K γ : ℕ) : ℤ) * c₀ : ℤ) : ℚ) • (1 : ℍ[ℚ, a₁, b₁])) ∈ R := by rw [← hxc]; exact (x γ).2
    have hF : Fγ γ p = c₀ • p := by
      rw [Fγ_eq]
      change E ε hε hε_hom (x γ : ℍ[ℚ, a₁, b₁]) (x γ).2 p = c₀ • p
      rw [E_congr ε hε hε_hom hxc (x γ).2 hxmem, E_intCast_smul_one ε hε hε_hom hε_one hε_add hR.one_mem,
        AddMonoidHom.smul_apply, AddMonoidHom.id_apply, mul_comm, ← smul_smul, natCast_zsmul,
        nsmul_eq_self_of_modEq (hK γ) hp]
    have hE1 : E A₀.act A₀.act_over A₀.act_hom _ hc1 p = c₀ • p := by
      rw [E_intCast_smul_one A₀.act A₀.act_over A₀.act_hom A₀.act_one A₀.act_add hΛ.one_mem,
        AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    have hdiff : (lab γ : ℍ[ℚ, a, b]) - (c₀ : ℚ) • (1 : ℍ[ℚ, a, b]) ∈ Λ := Λ.sub_mem (lab γ).2 hc1
    have hkill : E A₀.act A₀.act_over A₀.act_hom _ hdiff p = 0 := by
      rw [E_sub A₀.act A₀.act_over A₀.act_hom A₀.act_add _ _ (lab γ).2 hc1 hdiff, AddMonoidHom.sub_apply, hE1]
      change Eact (lab γ) p - c₀ • p = 0
      rw [hlab, hF, sub_self]
    exact annih _ hdiff hkill

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_fullLevel_eq_pushPt_act_of_isOrder_of_conj_of_pow_modEq_one (solution)
