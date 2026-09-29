-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/80ee2ba8-74a3-566c-814a-81f10abefdb5

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

namespace TwistCondAux

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem nsmulPt_add (p q : ℕ) (Q : SchemeHomOver t E.f) :
    nsmulPt E.L t (p + q) Q = E.L.mul t (nsmulPt E.L t p Q) (nsmulPt E.L t q Q) := by
  induction q with
  | zero => exact (E.L.mul_one t _).symm
  | succ q ih =>
    show E.L.mul t (nsmulPt E.L t (p + q) Q) Q = E.L.mul t (nsmulPt E.L t p Q) (E.L.mul t (nsmulPt E.L t q Q) Q)
    rw [ih, E.L.mul_assoc]

theorem nsmulPt_mul (i j : ℕ) (Q : SchemeHomOver t E.f) :
    nsmulPt E.L t i (nsmulPt E.L t j Q) = nsmulPt E.L t (j * i) Q := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show E.L.mul t (nsmulPt E.L t i (nsmulPt E.L t j Q)) (nsmulPt E.L t j Q) = nsmulPt E.L t (j * (i + 1)) Q
    rw [ih, Nat.mul_succ, nsmulPt_add]

theorem eq_one_of_mul_self {Q : SchemeHomOver t E.f} (hQ : E.L.mul t Q Q = Q) : Q = E.L.one t := by
  calc Q = E.L.mul t (E.L.one t) Q := (E.L.one_mul t Q).symm
    _ = E.L.mul t (E.L.mul t (E.L.inv t Q) Q) Q := by rw [E.L.inv_mul_cancel]
    _ = E.L.mul t (E.L.inv t Q) (E.L.mul t Q Q) := by rw [E.L.mul_assoc]
    _ = E.L.one t := by rw [hQ, E.L.inv_mul_cancel]

theorem act_one (x : ↥Λ) : pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t :=
  eq_one_of_mul_self E t (by rw [← E.act_hom, E.L.one_mul])

theorem act_nsmulPt (x : ↥Λ) (n : ℕ) (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L t n Q) = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) Q) := by
  induction n with
  | zero => exact act_one E t x
  | succ n ih =>
    show pushPt (E.act x) (E.act_over x) (E.L.mul t (nsmulPt E.L t n Q) Q) =
      E.L.mul t (nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) Q)) (pushPt (E.act x) (E.act_over x) Q)
    rw [E.act_hom, ih]

theorem act_mul_pt (hΛ : IsOrder Λ) (x y : ↥Λ) (Q : SchemeHomOver t E.f) :
    pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 y.2⟩)
        (E.act_over ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 y.2⟩) Q =
      pushPt (E.act x) (E.act_over x) (pushPt (E.act y) (E.act_over y) Q) := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, E.act_mul x y (hΛ.mul_mem x.2 y.2), Category.assoc]

theorem act_zero (Q : SchemeHomOver t E.f) : pushPt (E.act 0) (E.act_over 0) Q = E.L.one t :=
  eq_one_of_mul_self E t (by rw [← E.act_add, add_zero])

theorem act_nsmul (j : ℕ) (z : ↥Λ) (Q : SchemeHomOver t E.f) :
    pushPt (E.act (j • z)) (E.act_over (j • z)) Q = nsmulPt E.L t j (pushPt (E.act z) (E.act_over z) Q) := by
  induction j with
  | zero => rw [zero_smul]; exact act_zero E t Q
  | succ j ih =>
    rw [add_nsmul, one_nsmul, E.act_add, ih]
    rfl

theorem nsmulPt_comp {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (n : ℕ) (Q : SchemeHomOver t E.f) :
    schemeHomOverComp ψ hψ (nsmulPt E.L t n Q) = nsmulPt E.L t' n (schemeHomOverComp ψ hψ Q) := by
  induction n with
  | zero => exact E.L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (E.L.mul t (nsmulPt E.L t n Q) Q) =
      E.L.mul t' (nsmulPt E.L t' n (schemeHomOverComp ψ hψ Q)) (schemeHomOverComp ψ hψ Q)
    rw [E.L.mul_natural, ih]

end TwistCondAux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type u} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (c : ↥Λ) (h : FakeEllipticCurve.WithFullLevel.IsTwist c u u')
    (ℓ : ℕ) (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ)
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L₀)
    (hsurj : ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ →
      ∃ x z : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ (y : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (z : ℍ[ℚ, a, b]))
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk)) = u'.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) := by
  classical
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  set t := geomPoint k sk with ht

  let F : SchemeHomOver t u.1.f → SchemeHomOver t u'.1.f := fun Q => mapPt e.hom he Q
  have F_inj : Function.Injective F := by
    intro Q Q' hQ
    apply Subtype.ext
    have := congrArg Subtype.val hQ
    simp only [F, mapPt_coe] at this
    exact (cancel_mono e.hom).mp this
  have F_mul : ∀ Q Q', F (u.1.L.mul t Q Q') = u'.1.L.mul t (F Q) (F Q') := fun Q Q' => hmul t Q Q'
  have F_one : F (u.1.L.one t) = u'.1.L.one t :=
    TwistCondAux.eq_one_of_mul_self u'.1 t (by rw [← F_mul, u.1.L.one_mul])
  have F_nsmul : ∀ (j : ℕ) Q, F (nsmulPt u.1.L t j Q) = nsmulPt u'.1.L t j (F Q) := by
    intro j Q
    induction j with
    | zero => exact F_one
    | succ j ih =>
      show F (u.1.L.mul t (nsmulPt u.1.L t j Q) Q) = u'.1.L.mul t (nsmulPt u'.1.L t j (F Q)) (F Q)
      rw [F_mul, ih]
  have F_act : ∀ (x : ↥Λ) Q, F (pushPt (u.1.act x) (u.1.act_over x) Q) = pushPt (u'.1.act x) (u'.1.act_over x) (F Q) := by
    intro x Q
    apply Subtype.ext
    simp only [F, pushPt, mapPt_coe, Category.assoc, hact x]

  have F_sec : F (pushPt (u.1.act c) (u.1.act_over c) (FakeEllipticCurve.sectionAt u.2.P k sk)) =
      FakeEllipticCurve.sectionAt u'.2.P k sk := by
    apply Subtype.ext
    have hP1 : ((u.2.P).1 ≫ u.1.act c) ≫ e.hom = (u'.2.P).1 := by
      have := congrArg Subtype.val hP; simpa only [mapPt_coe, pushPt] using this
    simp only [F, mapPt_coe, pushPt, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc]
    rw [← ht, ← hP1, Category.assoc]

  let pt : ↥Λ → SchemeHomOver t u.1.f := fun y =>
    pushPt (u.1.act y) (u.1.act_over y) (nsmulPt u.1.L t (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk))
  let xc : ↥Λ → ↥Λ := fun x => ⟨(x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), hΛ.mul_mem x.2 c.2⟩

  have key : ∀ x : ↥Λ,
      pushPt (u'.1.act x) (u'.1.act_over x)
        (nsmulPt u'.1.L t (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk)) = F (pt (xc x)) := by
    intro x
    rw [← F_sec, ← F_nsmul, ← F_act]
    simp only [pt, xc]
    rw [TwistCondAux.act_mul_pt u.1 t hΛ x c, TwistCondAux.act_nsmulPt u.1 t c]

  have htors : ∀ z : ↥Λ, pt (ℓ • z) = u.1.L.one t := by
    intro z
    simp only [pt]
    rw [TwistCondAux.act_nsmul u.1 t ℓ z, TwistCondAux.act_nsmulPt u.1 t z, TwistCondAux.nsmulPt_mul u.1 t,
      Nat.div_mul_cancel hℓm]

    have h1 : pushPt (u.1.act z) (u.1.act_over z) (FakeEllipticCurve.sectionAt u.2.P k sk) =
        schemeHomOverComp t (Category.comp_id _) (pushPt (u.1.act z) (u.1.act_over z) u.2.P) := by
      apply Subtype.ext
      simp only [pushPt, mapPt_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc, ht]
    rw [h1, ← TwistCondAux.nsmulPt_comp u.1, ← TwistCondAux.act_nsmulPt u.1, u.2.torsion,
      TwistCondAux.act_one u.1, u.1.L.one_natural]

  have hdec : ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ → ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ pt y = pt (xc x) := by
    intro y hy
    obtain ⟨x, z, hx, hyx⟩ := hsurj y hy
    refine ⟨x, hx, ?_⟩
    have hy' : y = xc x + ℓ • z := by
      apply Subtype.ext
      simp only [xc, Submodule.coe_add, Submodule.coe_smul_of_tower, hyx, Nat.cast_smul_eq_nsmul]
    rw [hy']
    show pushPt (u.1.act (xc x + ℓ • z)) (u.1.act_over (xc x + ℓ • z)) _ = _
    rw [u.1.act_add]
    change u.1.L.mul t (pt (xc x)) (pt (ℓ • z)) = pt (xc x)
    rw [htors, u.1.L.mul_one]
  constructor
  ·
    intro H y hy hfac
    obtain ⟨x, hx, hyx⟩ := hdec y hy
    change FactorsThrough u.1.lev (pt y) at hfac
    change pt y = u.1.L.one t
    rw [hyx] at hfac ⊢
    have hfac' : FactorsThrough u'.1.lev (F (pt (xc x))) := (hlev t _).mp hfac
    rw [← key x] at hfac'
    have h1 := H x hx hfac'
    rw [key x, ← F_one] at h1
    exact F_inj h1
  ·
    intro H x hx hfac'
    rw [key x] at hfac' ⊢
    have hfac : FactorsThrough u.1.lev (pt (xc x)) := (hlev t _).mpr hfac'
    have h1 := H (xc x) (hL₀c _ hx) hfac
    change pt (xc x) = u.1.L.one t at h1
    rw [h1, F_one]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist (solution)
