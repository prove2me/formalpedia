-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwistVia_refl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/265518d0-c2c4-5dcf-9b69-c7281a889984

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace TwistFull

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
variable (E : FakeEllipticCurve Λ N S)

theorem act_one_pt (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  set y := pushPt (E.act x) (E.act_over x) (E.L.one t) with hy
  have h : E.L.mul t y y = y := by rw [hy, ← E.act_hom, E.L.one_mul]
  letI := E.L.pointGroup t
  have h2 : y * y = y * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h2

theorem act_nsmul (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n P) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) := by
  induction n with
  | zero => exact act_one_pt E x t
  | succ n ih => simp only [nsmulPt]; rw [E.act_hom, ih]

theorem act_comp (hΛ : IsOrder Λ) (x y : ↥Λ) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) P) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 y.2⟩) (E.act_over _) P := by
  apply Subtype.ext
  simp only [mapPt_coe, E.act_mul x y (hΛ.mul_mem x.2 y.2), Category.assoc]

theorem act_congr {x y : ↥Λ} (h : (x : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b])) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t E.f) : pushPt (E.act x) (E.act_over x) P = pushPt (E.act y) (E.act_over y) P := by
  have : x = y := Subtype.ext h
  subst this; rfl

theorem nsmulPt_comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t E.f) :
    schemeHomOverComp ψ hψ (nsmulPt E.L t n P) = nsmulPt E.L t' n (schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => simp only [nsmulPt]; exact E.L.one_natural t t' ψ hψ
  | succ n ih => simp only [nsmulPt]; rw [E.L.mul_natural t t' ψ hψ, ih]

theorem sectionAt_pushPt (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (k : Type) [Field k] (sk : S →+* k) :
    FakeEllipticCurve.sectionAt (pushPt (E.act x) (E.act_over x) P) k sk =
      pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) := by
  apply Subtype.ext
  simp only [FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, mapPt_coe, Category.assoc]

theorem natCast_mem (hΛ : IsOrder Λ) (m : ℕ) : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have h__af := (Λ.smul_mem (m : ℤ) hΛ.one_mem)
  simp at h__af
  exact h__af

theorem act_mul_natCast_sectionAt (hΛ : IsOrder Λ) {m : ℕ} (Pf : E.FullLevel m) (k : Type) [Field k] (sk : S →+* k)
    (z : ↥Λ) :
    pushPt (E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]) * (z : ℍ[ℚ, a, b]), hΛ.mul_mem (natCast_mem hΛ m) z.2⟩) (E.act_over _)
      (FakeEllipticCurve.sectionAt Pf.P k sk) = E.L.one (geomPoint k sk) := by
  rw [← act_comp E hΛ ⟨((m : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ m⟩ z,
    CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E hΛ.one_mem m (natCast_mem hΛ m),
    ← act_nsmul, FakeEllipticCurve.sectionAt, ← nsmulPt_comp, Pf.torsion, E.L.one_natural]
  exact act_one_pt E z _

end TwistFull

open TwistFull in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ P' : u.1.FullLevel m,
      FakeEllipticCurve.WithFullLevel.IsTwistVia c u ⟨u.1, P'⟩ (Iso.refl u.1.A) (Category.id_comp u.1.f) := by
  classical
  obtain ⟨E, Pf⟩ := u
  obtain ⟨y₁, hy₁⟩ := hcd
  obtain ⟨y₂, hy₂⟩ := hdc
  let P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f := pushPt (E.act c) (E.act_over c) Pf.P
  have htors : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P' = E.L.one (𝟙 (Spec (CommRingCat.of S))) := by
    simp only [P']
    rw [← act_nsmul, Pf.torsion, act_one_pt]
  have hgen : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
        ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = Q := by
    intro k _ _ sk Q hQ
    obtain ⟨x₀, hx₀⟩ := Pf.generates k sk Q hQ
    refine ⟨⟨(x₀ : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]), hΛ.mul_mem x₀.2 d.2⟩, ?_⟩
    simp only [P']
    rw [sectionAt_pushPt, act_comp E hΛ]
    have hmem : ((m : ℚ) : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])) ∈ Λ :=
      hΛ.mul_mem (natCast_mem hΛ m) (hΛ.mul_mem x₀.2 y₂.2)
    have key : (x₀ : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) =
        (x₀ : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])) := by
      have hdc' : (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = 1 + (m : ℚ) • (y₂ : ℍ[ℚ, a, b]) := by
        rw [← hy₂]; abel
      rw [mul_assoc, hdc', mul_add, mul_one, mul_smul_comm, Algebra.smul_def]
      congr 1
    rw [act_congr E (y := ⟨(x₀ : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])),
      Λ.add_mem x₀.2 hmem⟩) key]
    have hadd : (⟨(x₀ : ℍ[ℚ, a, b]) + ((m : ℚ) : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * (y₂ : ℍ[ℚ, a, b])), Λ.add_mem x₀.2 hmem⟩ : ↥Λ) =
        x₀ + ⟨_, hmem⟩ := rfl
    rw [hadd, E.act_add, act_mul_natCast_sectionAt E hΛ Pf k sk ⟨_, hΛ.mul_mem x₀.2 y₂.2⟩, E.L.mul_one]
    exact hx₀
  have hann : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ),
      pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = E.L.one (geomPoint k sk) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro k _ _ sk x
    simp only [P']
    rw [sectionAt_pushPt, act_comp E hΛ, Pf.annihilator k sk]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (y₁ : ℍ[ℚ, a, b]),
        Λ.sub_mem (hΛ.mul_mem y.2 d.2) (hΛ.mul_mem x.2 y₁.2)⟩, ?_⟩
      change (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) at hy
      change (x : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - (x : ℍ[ℚ, a, b]) * (y₁ : ℍ[ℚ, a, b]))
      rw [smul_sub, ← smul_mul_assoc, ← hy, ← mul_smul_comm, ← hy₁]
      noncomm_ring
    · rintro ⟨y, hy⟩
      refine ⟨⟨(y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), hΛ.mul_mem y.2 c.2⟩, ?_⟩
      change (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) at hy
      change (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]))
      rw [hy, smul_mul_assoc]
  let Pf' : E.FullLevel m := ⟨P', htors, hgen, hann⟩
  refine ⟨Pf', ?_⟩
  have hid : ∀ (h1 : (Iso.refl E.A).hom ≫ E.f = E.f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f),
      mapPt (Iso.refl E.A).hom h1 Q = Q := fun h1 {T} {t} Q => Subtype.ext (by simp [mapPt_coe])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [hid, hid, hid]
  · intro x; simp
  · intro T t P; rw [hid]
  · exact hid _ _

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwistVia_refl (solution)
