-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c195a4d8-ebe8-56eb-a099-a85d3ecea49c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

namespace ALComm

variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev aP (E : FakeEllipticCurve Λ N S) (m : ↥Λ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : SchemeHomOver t E.f :=
  pushPt (E.act m) (E.act_over m) P

section Action

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_coe (m : ↥Λ) (P : SchemeHomOver t E.f) : (aP E m P).1 = P.1 ≫ E.act m := rfl

theorem aP_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    aP E x (aP E y P) = aP E ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ P := by
  apply Subtype.ext
  simp only [aP_coe, Category.assoc, E.act_mul x y h]

theorem aP_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b])) (P : SchemeHomOver t E.f) :
    aP E x P = aP E y P := by
  obtain rfl : x = y := Subtype.ext h; rfl

theorem aP_add (x y : ↥Λ) (P : SchemeHomOver t E.f) :
    aP E (x + y) P = E.L.mul t (aP E x P) (aP E y P) := E.act_add x y t P

theorem aP_hom (m : ↥Λ) (P Q : SchemeHomOver t E.f) :
    aP E m (E.L.mul t P Q) = E.L.mul t (aP E m P) (aP E m Q) := E.act_hom m t P Q

theorem aP_one (m : ↥Λ) : aP E m (E.L.one t) = E.L.one t := by
  set x := aP E m (E.L.one t) with hx
  have hxx : E.L.mul t x x = x := by rw [hx, ← aP_hom, E.L.one_mul]
  letI := E.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem aP_unit (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) : aP E ⟨1, h1⟩ P = P := by
  apply Subtype.ext
  simp only [aP_coe, E.act_one h1, Category.comp_id]

theorem aP_zero (P : SchemeHomOver t E.f) : aP E 0 P = E.L.one t := by
  have h := aP_add E 0 0 P
  rw [add_zero] at h
  letI := E.L.pointGroup t
  have h2 : aP E 0 P * aP E 0 P = aP E 0 P * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

end Action

section Arithmetic

theorem intCast_mem (hΛ : IsOrder Λ) (z : ℤ) : (((z : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((z : ℚ)) : ℍ[ℚ, a, b]) = z • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one, coe_intCast]
  rw [this]; exact Λ.smul_mem z hΛ.one_mem

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : (((n : ℚ)) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := intCast_mem hΛ (n : ℤ); push_cast at this; exact this

def PCond (r : ℕ) (m : ℍ[ℚ, a, b]) : Prop :=
  ∃ n : ℤ, m * star m = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b])

theorem pcond_natCast (r : ℕ) : PCond (a := a) (b := b) r ((r : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨r, by rw [star_coe, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by norm_cast)⟩

theorem pcond_intCast_mul (r : ℕ) (z : ℤ) : PCond (a := a) (b := b) r (((z * r : ℤ) : ℚ) : ℍ[ℚ, a, b]) :=
  ⟨z * z * r, by rw [star_coe, ← coe_mul]; congr 1; push_cast; ring⟩

theorem pcond_mul (hΛ : IsOrder Λ) (r : ℕ) {m m' : ℍ[ℚ, a, b]} (hm : PCond r m) (hm' : m' ∈ Λ) :
    PCond r (m * m') := by
  obtain ⟨n, hn⟩ := hm
  obtain ⟨⟨k, hk⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hm'
  refine ⟨n * k, ?_⟩
  calc m * m' * star (m * m') = m * (m' * star m') * star m := by rw [star_mul]; simp only [mul_assoc]
    _ = m * ((nrd m' : ℚ) : ℍ[ℚ, a, b]) * star m := by rw [mul_star_eq_coe_nrd, mul_assoc]
    _ = ((k : ℚ) : ℍ[ℚ, a, b]) * (m * star m) := by rw [← hk, ← coe_commutes, mul_assoc]
    _ = (((((r : ℤ) : ℚ) * ((n * k : ℤ) : ℚ) : ℚ)) : ℍ[ℚ, a, b]) := by
        rw [hn, ← coe_mul]; exact congrArg (fun x : ℚ => (x : ℍ[ℚ, a, b])) (by push_cast; ring)

end Arithmetic

section Kernel

variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

def Kill (r : ℕ) (P : SchemeHomOver t E.f) : Prop :=
  ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((r : ℤ) * n : ℚ)) : ℍ[ℚ, a, b]) →
    aP E m P = E.L.one t

theorem kill_iff (r : ℕ) (P : SchemeHomOver t E.f) :
    Kill E r P ↔ ∀ m : ↥Λ, PCond r (m : ℍ[ℚ, a, b]) → aP E m P = E.L.one t :=
  ⟨fun h m ⟨n, hn⟩ => h m n hn, fun h m n hn => h m ⟨n, hn⟩⟩

theorem swap (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f)
    (A1 : ∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) :
    ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P) := by
  classical

  obtain ⟨A, B, hAB⟩ := hqq'.isCoprime

  let e₁ : ↥Λ := ⟨(((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  let e₂ : ↥Λ := ⟨(((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ _⟩
  have he : e₁ + e₂ = ⟨1, hΛ.one_mem⟩ := by
    apply Subtype.ext
    show (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) + (((B * q' : ℤ) : ℚ) : ℍ[ℚ, a, b]) = 1
    rw [← coe_add, ← coe_one]; congr 1; exact_mod_cast hAB
  let cq : ↥Λ := ⟨((q : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ q⟩
  let cA : ↥Λ := ⟨((A : ℚ) : ℍ[ℚ, a, b]), intCast_mem hΛ A⟩

  have hP₁ : Kill E q' (aP E e₁ P) := by
    rw [kill_iff]
    intro m hm

    have h1 : aP E cq (aP E m P) = E.L.one t := by
      have := A1 m hm; rw [kill_iff] at this
      exact this cq (pcond_natCast q)
    have hmem : ((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem cq.2 m.2
    rw [aP_mul E cq m hmem] at h1
    have hmem2 : ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem cA.2 hmem
    have h2 : aP E ⟨_, hmem2⟩ P = E.L.one t := by
      rw [← aP_mul E cA ⟨_, hmem⟩ hmem2, h1, aP_one]
    rw [aP_mul E m e₁ (hΛ.mul_mem m.2 e₁.2), ← h2]
    apply aP_congr
    show (m : ℍ[ℚ, a, b]) * (((A * q : ℤ) : ℚ) : ℍ[ℚ, a, b]) = ((A : ℚ) : ℍ[ℚ, a, b]) * (((q : ℚ) : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]))
    simp only [mul_coe_eq_smul, coe_mul_eq_smul, smul_smul]
    congr 1
    push_cast
    ring

  have hP₂ : ∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → aP E m' (aP E e₂ P) = E.L.one t := by
    intro m' hm'
    have := A1 e₂ (pcond_intCast_mul (a := a) (b := b) q' B); rw [kill_iff] at this
    exact this m' hm'

  intro m' hm'
  rw [kill_iff]
  intro m hm
  have hsplit : P = E.L.mul t (aP E e₁ P) (aP E e₂ P) := by
    rw [← aP_add, he, aP_unit]
  rw [hsplit, aP_hom, hP₂ m' hm', E.L.mul_one, aP_mul E m m' (hΛ.mul_mem m.2 m'.2)]
  rw [kill_iff] at hP₁
  exact hP₁ _ (pcond_mul hΛ q' hm m'.2)

theorem swap_iff (hΛ : IsOrder Λ) (q q' : ℕ) (hqq' : Nat.Coprime q q') (P : SchemeHomOver t E.f) :
    (∀ m : ↥Λ, PCond q' (m : ℍ[ℚ, a, b]) → Kill E q (aP E m P)) ↔
      (∀ m' : ↥Λ, PCond q (m' : ℍ[ℚ, a, b]) → Kill E q' (aP E m' P)) :=
  ⟨swap E hΛ q q' hqq' P, swap E hΛ q' q hqq'.symm P⟩

end Kernel

section Composite

variable {E E₁ E₁₂ : FakeEllipticCurve Λ N S}

theorem comp_eq_one_iff (r r' : ℕ)
    (φ₁ : E.A ⟶ E₁.A) (hφ₁ : φ₁ ≫ E₁.f = E.f) (φ₁₂ : E₁.A ⟶ E₁₂.A) (hφ₁₂ : φ₁₂ ≫ E₁₂.f = E₁.f)
    (hlin₁ : ∀ x : ↥Λ, E.act x ≫ φ₁ = φ₁ ≫ E₁.act x)
    (hker₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ₁ hφ₁ P = E₁.L.one t ↔ Kill E r P)
    (hker₁₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E₁.f),
      mapPt φ₁₂ hφ₁₂ Q = E₁₂.L.one t ↔ Kill E₁ r' Q)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = E₁₂.L.one t ↔
      ∀ m : ↥Λ, PCond r' (m : ℍ[ℚ, a, b]) → Kill E r (aP E m P) := by
  have hc : mapPt (φ₁ ≫ φ₁₂) (by rw [Category.assoc, hφ₁₂, hφ₁]) P = mapPt φ₁₂ hφ₁₂ (mapPt φ₁ hφ₁ P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  rw [hc, hker₁₂, kill_iff]
  refine forall_congr' fun m => forall_congr' fun _ => ?_
  have hl : aP E₁ m (mapPt φ₁ hφ₁ P) = mapPt φ₁ hφ₁ (aP E m P) :=
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hlin₁ m])
  rw [hl, hker₁]

end Composite

end ALComm

namespace ALComm
section ActNat
variable {S : Type u} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}

theorem aP_natCast (hΛ : IsOrder Λ) (n : ℕ) (P : SchemeHomOver t E.f) :
    aP E ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := Subtype.ext (by push_cast; rfl)
    rw [h0, aP_zero]; rfl
  | succ n ih =>
    have hs : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := Subtype.ext (by push_cast; rfl)
    rw [hs, aP_add, ih, aP_unit]; rfl

end ActNat
end ALComm

namespace LevelTorsorTR

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n P) P) = L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ P)) _
    rw [L.mul_natural, ih]

theorem pushPt_comp {φ : A ⟶ A} (hφ : φ ≫ f = f) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    pushPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (pushPt φ hφ P) :=
  Subtype.ext (by simp only [pushPt, mapPt_coe, schemeHomOverComp_coe, Category.assoc])

end LevelTorsorTR

open LevelTorsorTR ALComm in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : E.FullLevel m, P'.P = pushPt (E.act c) (E.act_over c) P.P ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨E, P'⟩ := by
  classical

  obtain ⟨y₁, hy₁⟩ := hcd
  obtain ⟨y₂, hy₂⟩ := hdc
  have hmΛ : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hΛ m

  let P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := pushPt (E.act c) (E.act_over c) P.P

  have act_nsmul : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (Q : SchemeHomOver t E.f),
      pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n Q) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) Q) := by
    intro x T t n Q
    induction n with
    | zero => exact aP_one E x
    | succ n ih =>
      show pushPt (E.act x) (E.act_over x) (E.L.mul t (nsmulPt E.L t n Q) Q) = E.L.mul t (nsmulPt E.L t n _) _
      rw [E.act_hom, ih]

  have hy₁' : (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) = 1 + ((m : ℚ) : ℍ[ℚ, a, b]) * (y₁ : ℍ[ℚ, a, b]) := by
    rw [coe_mul_eq_smul, ← hy₁]; abel
  have hy₂' : (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = 1 + ((m : ℚ) : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b]) := by
    rw [coe_mul_eq_smul, ← hy₂]; abel

  have secP' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      sectionAt P' k sk = aP E c (sectionAt P.P k sk) :=
    fun k _ _ sk => (pushPt_comp (E.act_over c) (geomPoint k sk) (Category.comp_id _) P.P).symm
  have kill_m : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (z : ↥Λ),
      aP E ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (z : ℍ[ℚ, a, b]), hΛ.mul_mem hmΛ z.2⟩ (sectionAt P.P k sk) = E.L.one (geomPoint k sk) := by
    intro k _ _ sk z
    have tors : nsmulPt E.L (geomPoint k sk) m (sectionAt P.P k sk) = E.L.one (geomPoint k sk) := by
      show nsmulPt E.L (geomPoint k sk) m (schemeHomOverComp (geomPoint k sk) (Category.comp_id _) P.P) = _
      rw [← nsmulPt_natural, P.torsion, E.L.one_natural]
    rw [← aP_mul E ⟨((m : ℚ) : ℍ[ℚ, a, b]), hmΛ⟩ z, show (⟨((m : ℚ) : ℍ[ℚ, a, b]), hmΛ⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ m⟩ from rfl,
      aP_natCast E hΛ m, ← act_nsmul, tors]
    exact aP_one E z
  refine ⟨⟨P', ?tors, ?gen, ?ann⟩, rfl, ?twist⟩
  case tors =>
    show nsmulPt E.L _ m (pushPt (E.act c) (E.act_over c) P.P) = _
    rw [← act_nsmul, P.torsion]; exact aP_one E c
  case gen =>
    intro k _ _ sk Q hQ
    obtain ⟨x, hx⟩ := P.generates k sk Q hQ
    refine ⟨⟨(x : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 d.2⟩, ?_⟩
    letI := E.L.pointGroup (geomPoint k sk)
    show aP E ⟨(x : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]), _⟩ (sectionAt P' k sk) = Q
    rw [secP', aP_mul E _ c (hΛ.mul_mem (hΛ.mul_mem x.2 d.2) c.2)]
    have e : ((x : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b])) * (c : ℍ[ℚ, a, b]) =
        (x : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])) := by
      rw [mul_assoc, hy₂', mul_add, mul_one, ← mul_assoc, ← coe_commutes, mul_assoc]
    rw [aP_congr E (y := x + ⟨((m : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])),
      hΛ.mul_mem hmΛ (hΛ.mul_mem x.2 y₂.2)⟩) e, aP_add, kill_m k sk ⟨_, hΛ.mul_mem x.2 y₂.2⟩]
    show aP E x (sectionAt P.P k sk) * 1 = Q
    rw [mul_one]; exact hx
  case ann =>
    intro k _ _ sk x
    show aP E x (sectionAt P' k sk) = E.L.one (geomPoint k sk) ↔ _
    rw [secP', aP_mul E x c (hΛ.mul_mem x.2 c.2), P.annihilator k sk]
    constructor
    · rintro ⟨y, hy⟩

      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (y₁ : ℍ[ℚ, a, b]),
        Λ.sub_mem (hΛ.mul_mem y.2 d.2) (hΛ.mul_mem x.2 y₁.2)⟩, ?_⟩
      have hy' : (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) := by
        rw [coe_mul_eq_smul]; exact hy
      show (x : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (y₁ : ℍ[ℚ, a, b]))
      rw [← coe_mul_eq_smul, mul_sub, ← mul_assoc, ← hy', mul_assoc, hy₁', mul_add, mul_one, ← mul_assoc,
        show (x : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) from (coe_commutes _ _).symm,
        mul_assoc, add_sub_cancel_right]
    · rintro ⟨y, hy⟩
      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), hΛ.mul_mem y.2 c.2⟩, ?_⟩
      show (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]))
      rw [hy, ← coe_mul_eq_smul, ← coe_mul_eq_smul, mul_assoc]
  case twist =>
    refine ⟨Iso.refl E.A, (Category.id_comp E.f), ?_, ?_, ?_, ?_⟩
    · intro T t X Y
      have : ∀ Z : SchemeHomOver t E.f, mapPt (Iso.refl E.A).hom (Category.id_comp E.f) Z = Z :=
        fun Z => Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
      rw [this, this, this]
    · intro x; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · intro T t X
      have : mapPt (Iso.refl E.A).hom (Category.id_comp E.f) X = X :=
        Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id])
      rw [this]
    · exact Subtype.ext (by simp only [mapPt_coe, Iso.refl_hom, Category.comp_id]; rfl)

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist (solution)
