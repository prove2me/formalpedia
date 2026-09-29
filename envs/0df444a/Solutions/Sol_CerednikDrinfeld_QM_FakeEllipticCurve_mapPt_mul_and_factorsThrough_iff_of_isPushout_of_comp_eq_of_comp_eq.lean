-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c7148b71-0746-57b7-92a9-af3be12b9e7e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
import Theorems.Thm_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian

noncomputable section

namespace MulLev

theorem lift_fst' {X Y S T : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (P : T ⟶ X) (Q : T ⟶ Y) (w : P ≫ f = Q ≫ g) :
    pullback.lift P Q w ≫ pullback.fst f g = P := pullback.lift_fst _ _ _
theorem lift_snd' {X Y S T : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (P : T ⟶ X) (Q : T ⟶ Y) (w : P ≫ f = Q ≫ g) :
    pullback.lift P Q w ≫ pullback.snd f g = Q := pullback.lift_snd _ _ _
theorem map_fst' {W X Y Z S T : Scheme.{0}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ := pullback.lift_fst _ _ _
theorem map_snd' {W X Y Z S T : Scheme.{0}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ := pullback.lift_snd _ _ _

def mulMor {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) :
    pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem mulMor_over {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) :
    mulMor L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

theorem mul_val_eq {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 = pullback.lift P.1 Q.1 (by rw [P.2, Q.2]) ≫ mulMor L := by
  have hψ : pullback.lift P.1 Q.1 (by rw [P.2, Q.2]) ≫ (pullback.fst f f ≫ f) = t := by
    rw [← Category.assoc, lift_fst', P.2]
  have hP : schemeHomOverComp _ hψ ⟨pullback.fst f f, rfl⟩ = P := Subtype.ext (lift_fst' _ _ _ _ _)
  have hQ : schemeHomOverComp _ hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = Q := Subtype.ext (lift_snd' _ _ _ _ _)
  have := L.mul_natural _ _ _ hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  rw [hP, hQ] at this
  rw [← this]
  rfl

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem mulMor_comp_eq {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f') (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    mulMor L' ≫ g = pullback.map f' f' f f g g (Spec.map (CommRingCat.ofHom φ)) hg.w.symm hg.w.symm ≫ mulMor L := by
  unfold mulMor
  rw [hmul, mul_val_eq L]
  have hlift : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, hg.w, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) =
      pullback.map f' f' f f g g (Spec.map (CommRingCat.ofHom φ)) hg.w.symm hg.w.symm := by
    apply pullback.hom_ext
    · exact (lift_fst' _ _ _ _ _).trans (map_fst' _ _ _ _ _ _ _ _ _).symm
    · exact (lift_snd' _ _ _ _ _).trans (map_snd' _ _ _ _ _ _ _ _ _).symm
  rw [← hlift]
  rfl

end MulLev

open MulLev in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (O : Type) [CommRing O] [IsLocalRing O]
    (E₀ : FakeEllipticCurve Λ 1 (ResidueField O))

    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (ρ : B →+* ResidueField O) (ρ' : B' →+* ResidueField O) (ρ'' : B'' →+* ResidueField O)
    (hρ : Function.Surjective ρ) (hρ' : Function.Surjective ρ') (hρ'' : Function.Surjective ρ'')
    (hρker : RingHom.ker ρ = maximalIdeal B) (hρ'ker : RingHom.ker ρ' = maximalIdeal B') (hρ''ker : RingHom.ker ρ'' = maximalIdeal B'')
    (hρψ : ρ.comp ψ = residue O) (hρ'ψ : ρ'.comp ψ' = residue O) (hρ''ψ : ρ''.comp ψ'' = residue O)
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hφ'ρ : ρ.comp φ' = ρ') (hφ''ρ : ρ.comp φ'' = ρ'')
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))

    (E' : FakeEllipticCurve Λ 1 B') (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ' E' E₀ g')
    (E'' : FakeEllipticCurve Λ 1 B'') (g'' : E₀.A ⟶ E''.A) (hg'' : FakeEllipticCurve.IsPullbackVia ρ'' E'' E₀ g'')

    (EB : FakeEllipticCurve Λ 1 B) (gB : E₀.A ⟶ EB.A) (hgB : FakeEllipticCurve.IsPullbackVia ρ EB E₀ gB)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'')
    (hgh' : gB ≫ h' = g') (hgh'' : gB ≫ h'' = g'')

    (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) E E₀ g)
    (k' : E'.A ⟶ E.A) (hk' : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
    (k'' : E''.A ⟶ E.A) (hk'' : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k'')
    (hgk' : g' ≫ k' = g) (hhk : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'')

    (Et : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (gt : E₀.A ⟶ Et.A)
    (hgt : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) Et E₀ gt)
    (kt' : E'.A ⟶ Et.A) (hkt' : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') Et E' kt')
    (kt'' : E''.A ⟶ Et.A) (hkt'' : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') Et E'' kt'')
    (hgkt' : g' ≫ kt' = gt) (hgkt'' : g'' ≫ kt'' = gt)

    (u : E.A ⟶ Et.A) (hu : u ≫ Et.f = E.f) (hk'u : k' ≫ u = kt') (hk''u : k'' ≫ u = kt'') :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
        mapPt u hu (E.L.mul t P Q) = Et.L.mul t (mapPt u hu P) (mapPt u hu Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt u hu P)) := by
  obtain ⟨sq', hmul', hact', hlev'⟩ := hk'
  obtain ⟨sq'', hmul'', hact'', hlev''⟩ := hk''
  obtain ⟨sqt', hmult', hactt', hlevt'⟩ := hkt'
  obtain ⟨sqt'', hmult'', hactt'', hlevt''⟩ := hkt''
  obtain ⟨sqh', hmulh', -, -⟩ := hh'
  obtain ⟨sqh'', hmulh'', -, -⟩ := hh''
  haveI : Smooth E.f := E.bundle.smooth

  obtain ⟨po, -, -⟩ := AlgebraicGeometry.isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat φ' φ'' hφ's hφ''s hφ'n hφ''n
    E.f E'.f E''.f EB.f h' sqh' h'' sqh'' k' sq' k'' sq'' hpo
    E.f E'.f E''.f EB.f h' sqh' h'' sqh'' k' sq' k'' sq'' hpo

  have key : mulMor E.L ≫ u = pullback.map E.f E.f Et.f Et.f u u (𝟙 _) (by rw [hu, Category.comp_id]) (by rw [hu, Category.comp_id]) ≫ mulMor Et.L := by
    apply po.hom_ext
    · rw [← Category.assoc, ← mulMor_comp_eq (pullbackFst φ' φ'') E.L E'.L k' sq' hmul', Category.assoc, hk'u,
        mulMor_comp_eq (pullbackFst φ' φ'') Et.L E'.L kt' sqt' hmult', ← Category.assoc]
      congr 1
      apply pullback.hom_ext <;> (try simp only [Category.assoc, map_fst', map_snd', lift_fst', lift_snd', mapPt_coe, hk'u]) <;> (try simp only [← Category.assoc, map_fst', map_snd', lift_fst', lift_snd', hk'u]) <;> (try simp only [Category.assoc, hk'u])
    · rw [← Category.assoc, ← mulMor_comp_eq (pullbackSnd φ' φ'') E.L E''.L k'' sq'' hmul'', Category.assoc, hk''u,
        mulMor_comp_eq (pullbackSnd φ' φ'') Et.L E''.L kt'' sqt'' hmult'', ← Category.assoc]
      congr 1
      apply pullback.hom_ext <;> (try simp only [Category.assoc, map_fst', map_snd', lift_fst', lift_snd', mapPt_coe, hk''u]) <;> (try simp only [← Category.assoc, map_fst', map_snd', lift_fst', lift_snd', hk''u]) <;> (try simp only [Category.assoc, hk''u])

  have hA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
      mapPt u hu (E.L.mul t P Q) = Et.L.mul t (mapPt u hu P) (mapPt u hu Q) := by
    intro T t P Q
    apply Subtype.ext
    rw [mapPt_coe, mul_val_eq E.L, mul_val_eq Et.L, Category.assoc, key, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> (try simp only [Category.assoc, map_fst', map_snd', lift_fst', lift_snd', mapPt_coe, hu]) <;> (try simp only [← Category.assoc, map_fst', map_snd', lift_fst', lift_snd', hu]) <;> (try simp only [Category.assoc, hu])
  refine ⟨hA, ?_⟩

  have hlev1 : ∀ {S : Type} [CommRing S] (F : FakeEllipticCurve Λ 1 S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t F.f), FactorsThrough F.lev P ↔ P = F.L.one t := by
    intro S _ F T t P
    constructor
    · intro hP
      have := F.lev_torsion t P hP
      change F.L.mul t (F.L.one t) P = F.L.one t at this
      rwa [F.L.one_mul] at this
    · rintro rfl; exact F.lev_one t

  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))),
      mapPt u hu (E.L.one t) = Et.L.one t := by
    intro T t
    set y := mapPt u hu (E.L.one t) with hy
    have hyy : Et.L.mul t y y = y := by rw [hy, ← hA, E.L.one_mul]
    calc y = Et.L.mul t (Et.L.mul t y y) (Et.L.inv t y) := by rw [Et.L.mul_assoc, Et.L.mul_inv_cancel, Et.L.mul_one]
      _ = Et.L.mul t y (Et.L.inv t y) := by rw [hyy]
      _ = Et.L.one t := Et.L.mul_inv_cancel _ _
  have hsurjfst : Function.Surjective (pullbackFst φ' φ'') := by
    intro b'; obtain ⟨b'', hb''⟩ := hφ''s (φ' b'); exact ⟨⟨(b', b''), by change φ' b' = φ'' b''; rw [hb'']⟩, rfl⟩
  have hnilfst : IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
    obtain ⟨N₀, hN₀⟩ := hφ''n
    have hN : RingHom.ker φ'' ^ (N₀ + 1) = ⊥ := by
      rw [Ideal.zero_eq_bot] at hN₀
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ N₀)).trans hN₀.le)
    refine ⟨N₀ + 1, ?_⟩
    have hle : RingHom.ker (pullbackFst φ' φ'') ≤ (RingHom.ker φ'').comap (pullbackSnd φ' φ'') := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := x.2
      change φ' x.1.1 = φ'' x.1.2 at this
      show φ'' x.1.2 = 0
      rw [← this]; change x.1.1 = 0 at hx; rw [hx, map_zero]
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    have h2' : (pullbackSnd φ' φ'') x = 0 := by
      have := Ideal.le_comap_pow _ (N₀ + 1) (Ideal.pow_right_mono hle (N₀ + 1) hx)
      rw [Ideal.mem_comap, hN, Ideal.mem_bot] at this
      exact this
    have h1 : x ∈ RingHom.ker (pullbackFst φ' φ'') := Ideal.pow_le_self (Nat.succ_ne_zero N₀) hx
    rw [RingHom.mem_ker] at h1
    rw [Ideal.mem_bot]
    exact Subtype.ext (Prod.ext h1 h2')
  haveI : IsIso u := AlgebraicGeometry.isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left (pullbackFst φ' φ'') hsurjfst hnilfst E.f Et.f u hu E'.f E'.f k' sq' kt' sqt' (𝟙 _)
    (by rw [hk'u, Category.id_comp])
  intro T t P
  rw [hlev1 E t P, hlev1 Et t (mapPt u hu P)]
  constructor
  · rintro rfl; exact hone t
  · intro h
    have : mapPt u hu P = mapPt u hu (E.L.one t) := by rw [h, hone]
    have h2 := congrArg Subtype.val this
    rw [mapPt_coe, mapPt_coe] at h2
    exact Subtype.ext ((cancel_mono u).1 h2)

#print axioms solution

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq (solution)
