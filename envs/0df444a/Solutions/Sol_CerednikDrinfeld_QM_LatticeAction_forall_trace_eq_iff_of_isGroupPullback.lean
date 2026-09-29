-- Prove2me | solution 1 for CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_of_isGroupPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d03301f9-7fb6-54b8-a0e0-9a77f95913f7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

noncomputable section

namespace TLocProof

variable {R' R'' : Type} [CommRing R'] [CommRing R''] {ψ : R' →+* R''}
  {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
  {L' : RelativeGroupLaw R' f'} {L'' : RelativeGroupLaw R'' f''} {h : A'' ⟶ A'}

theorem isPullback (hh : IsGroupPullback ψ L' L'' h) : IsPullback h f'' f' (Spec.map (CommRingCat.ofHom ψ)) :=
  hh.elim fun hP _ => hP

def castPt {S : Type} [CommRing S] {B : Scheme.{0}} {fB : B ⟶ Spec (CommRingCat.of S)} {T : Scheme.{0}}
    {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t') (P : SchemeHomOver t fB) : SchemeHomOver t' fB :=
  ⟨P.1, e ▸ P.2⟩

@[scoped simp] theorem castPt_val {S : Type} [CommRing S] {B : Scheme.{0}} {fB : B ⟶ Spec (CommRingCat.of S)} {T : Scheme.{0}}
    {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t') (P : SchemeHomOver t fB) : (castPt e P).1 = P.1 := rfl

theorem castPt_mul {S : Type} [CommRing S] {B : Scheme.{0}} {fB : B ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S fB)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t') (P Q : SchemeHomOver t fB) :
    castPt e (G.mul t P Q) = G.mul t' (castPt e P) (castPt e Q) := by
  subst e; rfl

def push (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R'')}
    (P : SchemeHomOver t f'') : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom ψ)) f' :=
  ⟨P.1 ≫ h, by rw [Category.assoc, (isPullback hh).w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem push_val (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R'')}
    (P : SchemeHomOver t f'') : (push hh P).1 = P.1 ≫ h := rfl

theorem push_mul (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R''))
    (P Q : SchemeHomOver t f'') : push hh (L''.mul t P Q) = L'.mul _ (push hh P) (push hh Q) := by
  obtain ⟨hP, hm⟩ := hh
  exact Subtype.ext (hm t P Q)

theorem push_injective (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R'')} :
    Function.Injective (push hh (T := T) (t := t)) := fun P Q e =>
  Subtype.ext ((isPullback hh).hom_ext (congrArg Subtype.val e) (by rw [P.2, Q.2]))

theorem push_surjective (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R'')} :
    Function.Surjective (push hh (T := T) (t := t)) := fun Q =>
  ⟨⟨(isPullback hh).lift Q.1 t (by rw [Q.2]), IsPullback.lift_snd _ _ _ _⟩,
    Subtype.ext (IsPullback.lift_fst _ _ _ _)⟩

theorem push_one (hh : IsGroupPullback ψ L' L'' h) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R'')) :
    push hh (L''.one t) = L'.one _ := by
  letI := L'.pointGroup (t ≫ Spec.map (CommRingCat.ofHom ψ))
  have e : push hh (L''.one t) * push hh (L''.one t) = push hh (L''.one t) := by
    show L'.mul _ (push hh (L''.one t)) (push hh (L''.one t)) = push hh (L''.one t)
    rw [← push_mul, L''.one_mul]
  exact mul_eq_left.mp e

section TangentLemmas

variable {S : Type} [CommRing S] (k : Type) [Field k]

theorem fstHom_comp_algebraMap_comp (sk : S →+* k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((algebraMap k (DualNumber k)).comp sk) = sk :=
  RingHom.ext fun r => by
    change (TrivSqZeroExt.fstHom k k k) (algebraMap k (DualNumber k) (sk r)) = sk r
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem scale_comp_algebraMap_comp (c : k) (sk : S →+* k) :
    (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom.comp
        ((algebraMap k (DualNumber k)).comp sk) = (algebraMap k (DualNumber k)).comp sk :=
  RingHom.ext fun r => by
    change (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))) (algebraMap k (DualNumber k) (sk r)) =
      algebraMap k (DualNumber k) (sk r)
    rw [AlgHom.commutes]

theorem tangentZero_comp_tangentBase (sk : S →+* k) : tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  simp only [tangentZero, tangentBase, geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    fstHom_comp_algebraMap_comp]

theorem tangentScale_comp_tangentBase (c : k) (sk : S →+* k) :
    tangentScale k c ≫ tangentBase k sk = tangentBase k sk := by
  simp only [tangentScale, tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scale_comp_algebraMap_comp]

theorem tangentBase_comp_specMap {S' : Type} [CommRing S'] (ψ : S →+* S') (sk : S' →+* k) :
    tangentBase k sk ≫ Spec.map (CommRingCat.ofHom ψ) = tangentBase k (sk.comp ψ) := by
  simp only [tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]

theorem geomPoint_comp_specMap {S' : Type} [CommRing S'] (ψ : S →+* S') (sk : S' →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom ψ) = geomPoint k (sk.comp ψ) := by
  simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end TangentLemmas

end TLocProof
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback.TLocProof"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R' R'' : Type} [CommRing R'] [CommRing R''] (ψ : R' →+* R'')
    {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
    (L' : RelativeGroupLaw R' f') (L'' : RelativeGroupLaw R'' f'') (h : A'' ⟶ A')
    (hh : IsGroupPullback ψ L' L'' h) (i' : LatticeAction Λ f' L') (i'' : LatticeAction Λ f'' L'')
    (hact : ∀ x : ↥Λ, i''.act x ≫ h = h ≫ i'.act x)
    (k : Type) [Field k] (sk : R'' →+* k) :
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f''),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f'', P ∈ Set.range τ ↔ IsTangentVector L'' k sk P) →
        (∀ v w : V, τ (v + w) = L''.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i''.act x) (i''.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) ↔
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (τ : V → SchemeHomOver (tangentBase k (sk.comp ψ)) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k (sk.comp ψ)) f', P ∈ Set.range τ ↔ IsTangentVector L' k (sk.comp ψ) P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k (sk.comp ψ)) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) := by

  have hbase : tangentBase k sk ≫ Spec.map (CommRingCat.ofHom ψ) = tangentBase k (sk.comp ψ) :=
    TLocProof.tangentBase_comp_specMap k ψ sk
  have hgeom : geomPoint k sk ≫ Spec.map (CommRingCat.ofHom ψ) = geomPoint k (sk.comp ψ) :=
    TLocProof.geomPoint_comp_specMap k ψ sk
  have hscale : ∀ c : k, tangentScale k c ≫ tangentBase k sk = tangentBase k sk := fun c =>
    TLocProof.tangentScale_comp_tangentBase k c sk
  have one_val_congr : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R')} (e : t₁ = t₂),
      (L'.one t₁).1 = (L'.one t₂).1 := by
    intro T t₁ t₂ e; subst e; rfl

  let Ph : SchemeHomOver (tangentBase k sk) f'' → SchemeHomOver (tangentBase k (sk.comp ψ)) f' :=
    fun P => TLocProof.castPt hbase (TLocProof.push hh P)
  have Phval : ∀ P, (Ph P).1 = P.1 ≫ h := fun P => rfl
  have Phinj : Function.Injective Ph := fun P Q e =>
    TLocProof.push_injective hh (Subtype.ext (by
      have e1 : (Ph P).1 = (Ph Q).1 := congrArg Subtype.val e
      rw [Phval, Phval] at e1
      exact e1))
  have Phsurj : Function.Surjective Ph := fun Q => by
    obtain ⟨P, hP⟩ := TLocProof.push_surjective hh (TLocProof.castPt hbase.symm Q)
    exact ⟨P, Subtype.ext (by rw [Phval, ← TLocProof.push_val hh P, hP]; rfl)⟩
  have Phmul : ∀ P Q, Ph (L''.mul _ P Q) = L'.mul _ (Ph P) (Ph Q) := fun P Q => by
    show TLocProof.castPt hbase (TLocProof.push hh (L''.mul _ P Q)) =
      L'.mul _ (TLocProof.castPt hbase (TLocProof.push hh P)) (TLocProof.castPt hbase (TLocProof.push hh Q))
    rw [TLocProof.push_mul, TLocProof.castPt_mul]
  have Phtan : ∀ P, IsTangentVector L' k (sk.comp ψ) (Ph P) ↔ IsTangentVector L'' k sk P := by
    intro P
    unfold IsTangentVector
    rw [Phval, ← Category.assoc]
    have h1 : (L'.one (geomPoint k (sk.comp ψ))).1 = (L''.one (geomPoint k sk)).1 ≫ h := by
      have := congrArg Subtype.val (TLocProof.push_one hh (geomPoint k sk))
      rw [TLocProof.push_val] at this
      rw [this]
      exact one_val_congr hgeom.symm
    rw [h1]
    constructor
    · intro e
      apply (TLocProof.isPullback hh).hom_ext e
      rw [Category.assoc, P.2, (L''.one (geomPoint k sk)).2]
      exact TLocProof.tangentZero_comp_tangentBase k sk
    · intro e; rw [e]
  have Phpush : ∀ (x : ↥Λ) P, Ph (pushPt (i''.act x) (i''.act_over x) P) = pushPt (i'.act x) (i'.act_over x) (Ph P) :=
    fun x P => Subtype.ext (by simp only [Phval, mapPt_coe, Category.assoc, hact])
  have Phscale : ∀ (c : k) (P Q : SchemeHomOver (tangentBase k sk) f''),
      (Ph Q).1 = tangentScale k c ≫ (Ph P).1 ↔ Q.1 = tangentScale k c ≫ P.1 := by
    intro c P Q
    rw [Phval, Phval, ← Category.assoc]
    constructor
    · intro e
      apply (TLocProof.isPullback hh).hom_ext e
      rw [Category.assoc, P.2, Q.2, hscale]
    · intro e; rw [e]

  let Phe : SchemeHomOver (tangentBase k sk) f'' ≃ SchemeHomOver (tangentBase k (sk.comp ψ)) f' :=
    Equiv.ofBijective Ph ⟨Phinj, Phsurj⟩
  have PhPhe : ∀ Q, Ph (Phe.symm Q) = Q := fun Q => Phe.apply_symm_apply Q
  have PhePh : ∀ P, Phe.symm (Ph P) = P := fun P => Phe.symm_apply_apply P
  constructor
  ·
    intro H V _ _ _ τ hinj hrange hadd hsmul x Φ hΦ n hn
    refine H V (fun v => Phe.symm (τ v)) (fun v w e => hinj (Phe.symm.injective e)) ?_ ?_ ?_ x Φ ?_ n hn
    · intro P
      rw [← Phtan, ← hrange]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        have hv' : Phe.symm (τ v) = P := hv
        rw [← hv', PhPhe]
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        show Phe.symm (τ v) = P
        rw [hv, PhePh]
    · intro v w
      show Phe.symm (τ (v + w)) = L''.mul _ (Phe.symm (τ v)) (Phe.symm (τ w))
      apply Phinj
      rw [PhPhe, Phmul, PhPhe, PhPhe, hadd]
    · intro c v
      show (Phe.symm (τ (c • v))).1 = tangentScale k c ≫ (Phe.symm (τ v)).1
      rw [← Phscale c, PhPhe, PhPhe]
      exact hsmul c v
    · intro v
      show Phe.symm (τ (Φ v)) = pushPt _ _ (Phe.symm (τ v))
      apply Phinj
      rw [PhPhe, Phpush, PhPhe, hΦ]
  ·
    intro H V _ _ _ τ hinj hrange hadd hsmul x Φ hΦ n hn
    refine H V (fun v => Ph (τ v)) (fun v w e => hinj (Phinj e)) ?_ ?_ ?_ x Φ ?_ n hn
    · intro Q
      obtain ⟨P, rfl⟩ := Phsurj Q
      rw [Phtan, ← hrange]
      constructor
      · rintro ⟨v, hv⟩; exact ⟨v, Phinj hv⟩
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        show Ph (τ v) = Ph P
        rw [hv]
    · intro v w
      show Ph (τ (v + w)) = L'.mul _ (Ph (τ v)) (Ph (τ w))
      rw [hadd, Phmul]
    · intro c v
      show (Ph (τ (c • v))).1 = tangentScale k c ≫ (Ph (τ v)).1
      rw [Phscale]
      exact hsmul c v
    · intro v
      show Ph (τ (Φ v)) = pushPt _ _ (Ph (τ v))
      rw [hΦ, Phpush]

end
end S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback (solution)
