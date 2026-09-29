-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_isPullback_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bf8b9047-185e-53a2-bd3e-512f3be63281

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace TraceGenericPt

section Transport

variable {K Ω : Type u} [CommRing K] [CommRing Ω] (ι : K →+* Ω)
  {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of Ω)} (LA : RelativeGroupLaw Ω fA)
  {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of K)} (L₀ : RelativeGroupLaw K f₀)
  (g : A ⟶ A₀) (hg : IsPullback g fA f₀ (Spec.map (CommRingCat.ofHom ι)))

def rebase (f : A₀ ⟶ Spec (CommRingCat.of K)) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of K)} (h : t₁ = t₂)
    (P : SchemeHomOver t₁ f) : SchemeHomOver t₂ f := ⟨P.1, P.2.trans h⟩

theorem rebase_mul {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of K)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f₀) : rebase f₀ h (L₀.mul t₁ P Q) = L₀.mul t₂ (rebase f₀ h P) (rebase f₀ h Q) := by
  subst h; rfl

def push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) : SchemeHomOver t₀ f₀ :=
  ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2, ht]⟩

@[scoped simp] theorem push_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) : (push ι g hg ht Q).1 = Q.1 ≫ g := rfl

private noncomputable def _root_.TraceGenericPt.lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) : SchemeHomOver t' fA :=
  ⟨hg.lift P.1 t' (by rw [P.2, ht]), hg.lift_snd _ _ _⟩

p2m_export "TraceGenericPt" "lift"
theorem lift_coe_g {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) : (lift ι g hg ht P).1 ≫ g = P.1 :=
  hg.lift_fst _ _ _

theorem push_lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P : SchemeHomOver t₀ f₀) :
    push ι g hg ht (lift ι g hg ht P) = P :=
  Subtype.ext (lift_coe_g ι g hg ht P)

theorem lift_push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (Q : SchemeHomOver t' fA) :
    lift ι g hg ht (push ι g hg ht Q) = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · rw [lift_coe_g]; rfl
  · rw [(lift ι g hg ht (push ι g hg ht Q)).2, Q.2]

theorem lift_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) : Function.Injective (lift ι g hg ht (fA := fA) (f₀ := f₀)) :=
  fun P Q h => by rw [← push_lift ι g hg ht P, ← push_lift ι g hg ht Q, h]

variable
  (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of Ω)) (P Q : SchemeHomOver t' fA),
      (LA.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom ι))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hg_mul in
theorem push_mul {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P Q : SchemeHomOver t' fA) :
    push ι g hg ht (LA.mul t' P Q) = L₀.mul t₀ (push ι g hg ht P) (push ι g hg ht Q) := by
  apply Subtype.ext
  change (LA.mul t' P Q).1 ≫ g = _
  rw [hg_mul]
  exact congrArg Subtype.val (rebase_mul L₀ ht _ _)

include hg_mul in
theorem lift_mul {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) (P Q : SchemeHomOver t₀ f₀) :
    lift ι g hg ht (L₀.mul t₀ P Q) = LA.mul t' (lift ι g hg ht P) (lift ι g hg ht Q) := by
  conv_lhs => rw [← push_lift ι g hg ht P, ← push_lift ι g hg ht Q]
  rw [← push_mul ι LA L₀ g hg hg_mul ht, lift_push]

include hg_mul in
theorem push_one {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) :
    push ι g hg ht (LA.one t') = L₀.one t₀ := by
  have hx : L₀.mul t₀ (push ι g hg ht (LA.one t')) (push ι g hg ht (LA.one t')) = push ι g hg ht (LA.one t') := by
    rw [← push_mul ι LA L₀ g hg hg_mul ht, LA.one_mul]
  calc push ι g hg ht (LA.one t')
      = L₀.mul t₀ (L₀.one t₀) (push ι g hg ht (LA.one t')) := (L₀.one_mul _ _).symm
    _ = L₀.mul t₀ (L₀.mul t₀ (L₀.inv t₀ (push ι g hg ht (LA.one t'))) (push ι g hg ht (LA.one t')))
          (push ι g hg ht (LA.one t')) := by rw [L₀.inv_mul_cancel]
    _ = L₀.mul t₀ (L₀.inv t₀ (push ι g hg ht (LA.one t')))
          (L₀.mul t₀ (push ι g hg ht (LA.one t')) (push ι g hg ht (LA.one t'))) := L₀.mul_assoc _ _ _ _
    _ = L₀.mul t₀ (L₀.inv t₀ (push ι g hg ht (LA.one t'))) (push ι g hg ht (LA.one t')) := by rw [hx]
    _ = L₀.one t₀ := L₀.inv_mul_cancel _ _

include hg_mul in
theorem one_coe_g {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of Ω)} {t₀ : T ⟶ Spec (CommRingCat.of K)}
    (ht : t' ≫ Spec.map (CommRingCat.ofHom ι) = t₀) : (LA.one t').1 ≫ g = (L₀.one t₀).1 :=
  congrArg Subtype.val (push_one ι LA L₀ g hg hg_mul ht)

end Transport

section Bases

variable {K Ω : Type u} [CommRing K] [CommRing Ω] (ι : K →+* Ω)

theorem geomPoint_comp (k : Type u) [Field k] (s : Ω →+* k) :
    geomPoint k s ≫ Spec.map (CommRingCat.ofHom ι) = geomPoint k (s.comp ι) := by
  rw [geomPoint, geomPoint, ← Spec.map_comp]; rfl

theorem tangentBase_comp (k : Type u) [Field k] (s : Ω →+* k) :
    tangentBase k s ≫ Spec.map (CommRingCat.ofHom ι) = tangentBase k (s.comp ι) := by
  rw [tangentBase, tangentBase, ← Spec.map_comp]; rfl

theorem tangentZero_tangentBase (k : Type u) [Field k] (s : Ω →+* k) :
    tangentZero k ≫ tangentBase k s = geomPoint k s := by
  have h : CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp s) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom = CommRingCat.ofHom s := by
    ext r; first | rfl | simp
  rw [tangentZero, tangentBase, geomPoint, ← Spec.map_comp, h]

theorem tangentScale_tangentBase (k : Type u) [Field k] (s : Ω →+* k) (c : k) :
    tangentScale k c ≫ tangentBase k s = tangentBase k s := by
  have h : CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp s) ≫
      CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom =
      CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp s) := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact AlgHom.commutes _ _
  rw [tangentScale, tangentBase, ← Spec.map_comp, h]

end Bases

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem main
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E₀ : FakeEllipticCurve Λ N S')
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ act x)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (s : S' →+* k) (hs : s.comp φ = sk) :
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) := by
  intro V _ _ _ τ hinj hrange hadd hscale m Φ hΦ n hn
  have htb : tangentBase k s ≫ Spec.map (CommRingCat.ofHom φ) = tangentBase k sk := by
    rw [tangentBase_comp, hs]
  have hgp : geomPoint k s ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k sk := by
    rw [geomPoint_comp, hs]

  let τ' : V → SchemeHomOver (tangentBase k s) E₀.f := fun v => lift φ g hg htb (τ v)
  have hτ'g : ∀ v, (τ' v).1 ≫ g = (τ v).1 := fun v => lift_coe_g φ g hg htb (τ v)
  have hone : (E₀.L.one (geomPoint k s)).1 ≫ g = (L.one (geomPoint k sk)).1 :=
    one_coe_g φ E₀.L L g hg hg_mul hgp
  refine E₀.act_trace k s V τ' ?_ ?_ ?_ ?_ m Φ ?_ n hn
  · exact (lift_injective φ g hg htb).comp hinj
  · intro P
    constructor
    · rintro ⟨v, rfl⟩
      have hv : IsTangentVector L k sk (τ v) := (hrange (τ v)).mp ⟨v, rfl⟩
      change tangentZero k ≫ (τ' v).1 = (E₀.L.one (geomPoint k s)).1
      apply hg.hom_ext
      · rw [Category.assoc, hτ'g, hone]; exact hv
      · rw [Category.assoc, (τ' v).2, (E₀.L.one (geomPoint k s)).2, tangentZero_tangentBase]
    · intro hP
      have hP' : IsTangentVector L k sk (push φ g hg htb P) := by
        change tangentZero k ≫ (P.1 ≫ g) = (L.one (geomPoint k sk)).1
        rw [← Category.assoc, show tangentZero k ≫ P.1 = _ from hP, hone]
      obtain ⟨v, hv⟩ := (hrange _).mpr hP'
      exact ⟨v, by change lift φ g hg htb (τ v) = P; rw [hv, lift_push]⟩
  · intro v w
    change lift φ g hg htb (τ (v + w)) =
      E₀.L.mul _ (lift φ g hg htb (τ v)) (lift φ g hg htb (τ w))
    rw [hadd, lift_mul φ E₀.L L g hg hg_mul htb]
  · intro c v
    apply hg.hom_ext
    · rw [Category.assoc, hτ'g, hτ'g, hscale]
    · rw [Category.assoc, (τ' (c • v)).2, (τ' v).2, tangentScale_tangentBase]
  · intro v
    apply Subtype.ext
    apply hg.hom_ext
    · change (τ' (Φ v)).1 ≫ g = ((τ' v).1 ≫ E₀.act m) ≫ g
      rw [hτ'g, hΦ, Category.assoc, hg_act, ← Category.assoc, hτ'g]; rfl
    · rw [(τ' (Φ v)).2, (pushPt (E₀.act m) (E₀.act_over m) (τ' v)).2]

end TraceGenericPt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq.TraceGenericPt"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E₀ : FakeEllipticCurve Λ N S')
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ act x)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (s : S' →+* k) (hs : s.comp φ = sk) :
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) :=
  TraceGenericPt.main φ E₀ L act act_over g hg hg_mul hg_act k sk s hs

end S_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_isPullback_of_comp_eq (solution)
