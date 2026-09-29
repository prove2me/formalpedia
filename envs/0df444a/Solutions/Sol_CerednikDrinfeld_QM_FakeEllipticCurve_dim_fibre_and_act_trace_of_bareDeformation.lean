-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.dim_fibre_and_act_trace_of_bareDeformation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/12876a88-ec81-5c79-8c34-cc03c0ffafad

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing"

open scoped Quaternion TensorProduct NumberField

open CategoryTheory.Limits

universe u

namespace E160DT

theorem preimage_singleton_eq_image {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s : Spec (CommRingCat.of T)) :
    f.base ⁻¹' {Spec.map (CommRingCat.ofHom π) s} = g.base '' (f₀.base ⁻¹' {s}) := by
  have hgH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker f f₀ g hg
  obtain ⟨_, hgsurj, _⟩ := hgH
  have hbH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom π)) IsPullback.of_id_snd
  obtain ⟨_, _, hbhomeo⟩ := hbH
  have hw : ∀ x₀ : A₀, f.base (g.base x₀) = (Spec.map (CommRingCat.ofHom π)).base (f₀.base x₀) := by
    intro x₀
    have := congrArg (fun k => k.base x₀) hg.w
    simpa using this
  ext x
  constructor
  · intro hx
    obtain ⟨x₀, rfl⟩ := g.surjective x
    refine ⟨x₀, ?_, rfl⟩
    have h1 : (Spec.map (CommRingCat.ofHom π)).base (f₀.base x₀) =
        (Spec.map (CommRingCat.ofHom π)).base s := by
      rw [← hw]; simpa using hx
    exact hbhomeo.injective h1
  · rintro ⟨x₀, hx₀, rfl⟩
    have hx₀' : f₀.base x₀ = s := by simpa using hx₀
    rw [Set.mem_preimage, Set.mem_singleton_iff, hw, hx₀']

theorem topologicalKrullDim_fibre_eq {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s : Spec (CommRingCat.of T')) :
    ∃ s₀ : Spec (CommRingCat.of T),
      topologicalKrullDim ↥(f.base ⁻¹' {s}) = topologicalKrullDim ↥(f₀.base ⁻¹' {s₀}) := by
  have hbH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom π)) IsPullback.of_id_snd
  obtain ⟨_, _, _⟩ := hbH
  obtain ⟨s₀, rfl⟩ := (Spec.map (CommRingCat.ofHom π)).surjective s
  refine ⟨s₀, ?_⟩
  have hgH := AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    π hπ hker f f₀ g hg
  obtain ⟨_, _, hhomeo⟩ := hgH
  rw [preimage_singleton_eq_image π hπ hker f₀ f g hg s₀]
  let e := hhomeo.homeomorph _
  have he : (e : A₀ → A) = g.base := rfl
  have := IsHomeomorph.topologicalKrullDim_eq _ (e.image (f₀.base ⁻¹' {s₀})).isHomeomorph
  rw [he] at this
  exact this.symm

end E160DT

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw BareDeformation"
namespace BareDeformation
p2m_export "GoodReductionJacobian.BareDeformation" "hom A cart L g f"
p2m_open "GoodReductionJacobian.BareDeformation GoodReductionJacobian"

section Lift

variable {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
  {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  (D : BareDeformation fₛ Lₛ B)

private theorem _root_.GoodReductionJacobian.BareDeformation.ext_g {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q Q' : SchemeHomOver t fₛ)
    (h : Q.1 ≫ D.g = Q'.1 ≫ D.g) : Q = Q' := by
  apply Subtype.ext
  exact D.cart.hom_ext h (by rw [Q.2, Q'.2])

p2m_export "GoodReductionJacobian.BareDeformation" "ext_g"

private def _root_.GoodReductionJacobian.BareDeformation.pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (Q : SchemeHomOver t fₛ) :
    SchemeHomOver t' D.f :=
  ⟨Q.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, Q.2, ht]⟩

p2m_export "GoodReductionJacobian.BareDeformation" "pushG"
@[scoped simp] theorem pushG_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    (D.pushG t t' ht Q).1 = Q.1 ≫ D.g := rfl

private noncomputable def _root_.GoodReductionJacobian.BareDeformation.liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (P : SchemeHomOver t' D.f) :
    SchemeHomOver t fₛ :=
  ⟨D.cart.lift P.1 t (by rw [P.2, ht]), D.cart.lift_snd _ _ _⟩

p2m_export "GoodReductionJacobian.BareDeformation" "liftG"
@[scoped simp] private theorem _root_.GoodReductionJacobian.BareDeformation.liftG_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    (D.liftG t t' ht P).1 ≫ D.g = P.1 :=
  D.cart.lift_fst _ _ _

p2m_export "GoodReductionJacobian.BareDeformation" "liftG_g"
private theorem _root_.GoodReductionJacobian.BareDeformation.pushG_liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    D.pushG t t' ht (D.liftG t t' ht P) = P :=
  Subtype.ext (D.liftG_g t t' ht P)

p2m_export "GoodReductionJacobian.BareDeformation" "pushG_liftG"
private theorem _root_.GoodReductionJacobian.BareDeformation.liftG_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    D.liftG t t' ht (D.pushG t t' ht Q) = Q :=
  D.ext_g _ _ (by rw [liftG_g, pushG_coe])

p2m_export "GoodReductionJacobian.BareDeformation" "liftG_pushG"

private theorem _root_.GoodReductionJacobian.BareDeformation.mul_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
    (P Q : SchemeHomOver t fₛ) :
    (D.L.mul t' (D.pushG t t' ht P) (D.pushG t t' ht Q)).1 = (Lₛ.mul t P Q).1 ≫ D.g := by
  subst ht
  rw [D.hom t P Q]
  rfl

p2m_export "GoodReductionJacobian.BareDeformation" "mul_pushG"

private theorem _root_.GoodReductionJacobian.BareDeformation.one_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) :
    (Lₛ.one t).1 ≫ D.g = (D.L.one t').1 := by
  set u := D.pushG t t' ht (Lₛ.one t) with hu
  have h1 : D.L.mul t' u u = u := by
    apply Subtype.ext
    rw [hu, D.mul_pushG t t' ht, Lₛ.one_mul, pushG_coe]
  letI := D.L.pointGroup t'
  have h2 : u = 1 := mul_eq_left.mp h1
  have h3 : u.1 = (D.L.one t').1 := congrArg Subtype.val h2
  rw [← h3, hu, pushG_coe]

p2m_export "GoodReductionJacobian.BareDeformation" "one_g"
end Lift

end GoodReductionJacobian.BareDeformation
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian.BareDeformation"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian"

namespace E160DT

theorem tangentZero_tangentBase {S : Type} [CommRing S] (k : Type) [Field k] (sk : S →+* k) :
    tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  have h : (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((algebraMap k (DualNumber k)).comp sk) = sk := by
    ext x
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  simp only [tangentZero, tangentBase, geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tangentScale_tangentBase {S : Type} [CommRing S] (k : Type) [Field k] (sk : S →+* k) (c : k) :
    tangentScale k c ≫ tangentBase k sk = tangentBase k sk := by
  have h : (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom.comp
      ((algebraMap k (DualNumber k)).comp sk) = (algebraMap k (DualNumber k)).comp sk := by
    ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
  simp only [tangentScale, tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tangentBase_comp {B B₀ : Type} [CommRing B] [CommRing B₀] (π : B →+* B₀)
    (k : Type) [Field k] (sk₀ : B₀ →+* k) :
    tangentBase k (sk₀.comp π) = tangentBase k sk₀ ≫ Spec.map (CommRingCat.ofHom π) := by
  simp only [tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]

theorem geomPoint_comp {B B₀ : Type} [CommRing B] [CommRing B₀] (π : B →+* B₀)
    (k : Type) [Field k] (sk₀ : B₀ →+* k) :
    geomPoint k (sk₀.comp π) = geomPoint k sk₀ ≫ Spec.map (CommRingCat.ofHom π) := by
  simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem one_coe_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

end E160DT
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.GoodReductionJacobian.BareDeformation"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ D.g = D.g ≫ act x) :
    (∀ s : ↥(Spec (CommRingCat.of B)), topologicalKrullDim ↥(D.f.base ⁻¹' {s}) = 2) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) D.f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) D.f, P ∈ Set.range τ ↔ IsTangentVector D.L k sk P) →
      (∀ v w : V, τ (v + w) = D.L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k)) := by
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨s₀, hs₀⟩ := E160DT.topologicalKrullDim_fibre_eq (algebraMap B B₀) hπ hker E₀.f D.f D.g D.cart s
    rw [hs₀]
    exact E₀.dim_fibre s₀
  intro k _ _ sk V _ _ _ τ hτinj hτrange hτadd hτsmul m Φ hΦ n hn

  have hle : RingHom.ker (algebraMap B B₀) ≤ RingHom.ker sk := by
    intro x hx
    obtain ⟨N, hN⟩ := hker
    have hxN : x ^ N ∈ RingHom.ker (algebraMap B B₀) ^ N := Ideal.pow_mem_pow hx N
    rw [hN] at hxN
    have hx0 : x ^ N = 0 := by simpa using hxN
    have : IsNilpotent (sk x) := ⟨N, by rw [← map_pow, hx0, map_zero]⟩
    exact (RingHom.mem_ker).mpr this.eq_zero
  obtain ⟨sk₀, hsk⟩ : ∃ sk₀ : B₀ →+* k, sk₀.comp (algebraMap B B₀) = sk :=
    ⟨(RingHom.liftOfSurjective (algebraMap B B₀) hπ) ⟨sk, hle⟩,
      RingHom.liftOfSurjective_comp (algebraMap B B₀) hπ ⟨sk, hle⟩⟩
  subst hsk
  have hTB := E160DT.tangentBase_comp (algebraMap B B₀) k sk₀

  let τ₀ : V → SchemeHomOver (tangentBase k sk₀) E₀.f := fun v => D.liftG _ _ hTB (τ v)
  have hτ₀g : ∀ v, (τ₀ v).1 ≫ D.g = (τ v).1 := fun v => D.liftG_g _ _ hTB (τ v)
  have hpush : ∀ v, D.pushG _ _ hTB (τ₀ v) = τ v := fun v => D.pushG_liftG _ _ hTB (τ v)

  have h1 : Function.Injective τ₀ := by
    intro v w hvw
    apply hτinj
    rw [← hpush v, ← hpush w, hvw]

  have h2 : ∀ P : SchemeHomOver (tangentBase k sk₀) E₀.f, P ∈ Set.range τ₀ ↔ IsTangentVector E₀.L k sk₀ P := by
    intro P
    have hD : D.pushG _ _ hTB P ∈ Set.range τ ↔
        IsTangentVector D.L k (sk₀.comp (algebraMap B B₀)) (D.pushG _ _ hTB P) := hτrange _
    have hrange : P ∈ Set.range τ₀ ↔ D.pushG _ _ hTB P ∈ Set.range τ := by
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨v, (hpush v).symm⟩
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        show D.liftG _ _ hTB (τ v) = P
        rw [hv, D.liftG_pushG]
    rw [hrange, hD]
    unfold IsTangentVector
    rw [GoodReductionJacobian.BareDeformation.pushG_coe, ← Category.assoc,
      ← E160DT.one_coe_congr D.L (E160DT.geomPoint_comp (algebraMap B B₀) k sk₀).symm,
      ← D.one_g (geomPoint k sk₀) _ rfl]
    constructor
    · intro h
      exact D.cart.hom_ext h (by
        rw [Category.assoc, P.2, (E₀.L.one (geomPoint k sk₀)).2, E160DT.tangentZero_tangentBase])
    · intro h; rw [h]

  have h3 : ∀ v w : V, τ₀ (v + w) = E₀.L.mul (tangentBase k sk₀) (τ₀ v) (τ₀ w) := by
    intro v w
    apply D.ext_g
    rw [hτ₀g, hτadd, ← D.mul_pushG _ _ hTB, hpush, hpush]

  have h4 : ∀ (c : k) (v : V), (τ₀ (c • v)).1 = tangentScale k c ≫ (τ₀ v).1 := by
    intro c v
    apply D.cart.hom_ext
    · rw [hτ₀g, hτsmul, Category.assoc, hτ₀g]
    · rw [(τ₀ (c • v)).2, Category.assoc, (τ₀ v).2, E160DT.tangentScale_tangentBase]

  have h5 : ∀ v : V, τ₀ (Φ v) = pushPt (E₀.act m) (E₀.act_over m) (τ₀ v) := by
    intro v
    apply D.ext_g
    rw [hτ₀g, hΦ]
    show (τ v).1 ≫ act m = ((τ₀ v).1 ≫ E₀.act m) ≫ D.g
    rw [Category.assoc, hact, ← Category.assoc, hτ₀g]
  exact E₀.act_trace k sk₀ V τ₀ h1 h2 h3 h4 m Φ h5 n hn

end S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation (solution)
