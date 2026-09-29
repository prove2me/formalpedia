-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/47054058-50ab-5208-a3f6-5663dbc0c1d3

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian

namespace FPUniq

theorem comp_pullbackFst_eq_comp_pullbackSnd {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) :
    φ'.comp (pullbackFst φ' φ'') = φ''.comp (pullbackSnd φ' φ'') := by
  ext x
  exact x.2

theorem isNilpotent_ker_pullbackFst {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hn : IsNilpotent (RingHom.ker φ'')) :
    IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
  obtain ⟨N₀, hN₀⟩ := hn
  have hN : RingHom.ker φ'' ^ (N₀ + 1) = 0 := by
    rw [Ideal.zero_eq_bot] at hN₀ ⊢
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ N₀)).trans hN₀.le)
  refine ⟨N₀ + 1, ?_⟩
  set N := N₀ + 1 with hNdef
  have hle : RingHom.ker (pullbackFst φ' φ'') ≤ (RingHom.ker φ'').comap (pullbackSnd φ' φ'') := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := x.2
    change φ' x.1.1 = φ'' x.1.2 at this
    show φ'' x.1.2 = 0
    rw [← this]
    change x.1.1 = 0 at hx
    rw [hx, map_zero]
  rw [Ideal.zero_eq_bot] at hN ⊢
  rw [eq_bot_iff]
  intro x hx
  have h2 : x ∈ ((RingHom.ker φ'').comap (pullbackSnd φ' φ'')) ^ N := Ideal.pow_right_mono hle N hx
  have h2' : (pullbackSnd φ' φ'') x = 0 := by
    have := Ideal.le_comap_pow _ N h2
    rw [Ideal.mem_comap, hN, Ideal.mem_bot] at this
    exact this
  have h1 : x ∈ RingHom.ker (pullbackFst φ' φ'') := Ideal.pow_le_self (by rw [hNdef]; exact Nat.succ_ne_zero N₀) hx
  rw [RingHom.mem_ker] at h1
  rw [Ideal.mem_bot]
  apply Subtype.ext
  exact Prod.ext h1 h2'

theorem surjective_pullbackFst {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hs : Function.Surjective φ'') :
    Function.Surjective (pullbackFst φ' φ'') := by
  intro b'
  obtain ⟨b'', hb''⟩ := hs (φ' b')
  exact ⟨⟨(b', b''), by change φ' b' = φ'' b''; rw [hb'']⟩, rfl⟩

end FPUniq

open FPUniq in
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
    (hgkt' : g' ≫ kt' = gt) (hgkt'' : g'' ≫ kt'' = gt) :
    ∃ (e : E.A ≅ Et.A) (he : e.hom ≫ Et.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
        mapPt e.hom he (E.L.mul t P Q) = Et.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ Et.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt e.hom he P)) ∧
      k' ≫ e.hom = kt' ∧ k'' ≫ e.hom = kt'' ∧ g ≫ e.hom = gt := by
  obtain ⟨sq', hmul', hact', hlev'⟩ := hk'
  obtain ⟨sq'', hmul'', hact'', hlev''⟩ := hk''
  obtain ⟨sqt', hmult', hactt', hlevt'⟩ := hkt'
  obtain ⟨sqt'', hmult'', hactt'', hlevt''⟩ := hkt''

  have hPB : φ'.comp (pullbackFst φ' φ'') = φ''.comp (pullbackSnd φ' φ'') := comp_pullbackFst_eq_comp_pullbackSnd φ' φ''
  have hr1 : FakeEllipticCurve.IsPullbackVia (φ'.comp (pullbackFst φ' φ'')) Et EB (h' ≫ kt') :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (pullbackFst φ' φ'') φ' Et E' EB kt' h' ⟨sqt', hmult', hactt', hlevt'⟩ hh'
  have hr2 : FakeEllipticCurve.IsPullbackVia (φ'.comp (pullbackFst φ' φ'')) Et EB (h'' ≫ kt'') := by
    rw [hPB]
    exact CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (pullbackSnd φ' φ'') φ'' Et E'' EB kt'' h'' ⟨sqt'', hmult'', hactt'', hlevt''⟩ hh''
  have hagree : h' ≫ kt' = h'' ≫ kt'' := by
    apply CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
      (ResidueField O) B ρ hρ hρker E₀ EB gB hgB _ Et (φ'.comp (pullbackFst φ' φ'')) (h' ≫ kt') (h'' ≫ kt'') hr1 hr2
    rw [← Category.assoc, hgh', hgkt', ← Category.assoc, hgh'', hgkt'']

  let e₁ : E.A ⟶ Et.A := hpo.desc kt' kt'' hagree
  have hk'e : k' ≫ e₁ = kt' := hpo.inl_desc _ _ _
  have hk''e : k'' ≫ e₁ = kt'' := hpo.inr_desc _ _ _
  have he₁ : e₁ ≫ Et.f = E.f := by
    apply hpo.hom_ext
    · rw [← Category.assoc, hk'e, sqt'.w, sq'.w]
    · rw [← Category.assoc, hk''e, sqt''.w, sq''.w]

  haveI : Smooth E.f := E.bundle.smooth
  haveI : IsIso e₁ :=
    AlgebraicGeometry.isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left (pullbackFst φ' φ'') (surjective_pullbackFst φ' φ'' hφ''s) (isNilpotent_ker_pullbackFst φ' φ'' hφ''n)
      E.f Et.f e₁ he₁ E'.f E'.f k' sq' kt' sqt' (𝟙 _) (by rw [hk'e, Category.id_comp])

  obtain ⟨hmul, hlev⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq O E₀ B B' B'' ψ ψ' ψ'' ρ ρ' ρ'' hρ hρ' hρ'' hρker hρ'ker hρ''ker hρψ hρ'ψ hρ''ψ φ' φ'' hφ' hφ''
    hφ'ρ hφ''ρ hφ's hφ''s hφ'n hφ''n E' g' hg' E'' g'' hg'' EB gB hgB h' hh' h'' hh'' hgh' hgh''
    E g hg k' ⟨sq', hmul', hact', hlev'⟩ k'' ⟨sq'', hmul'', hact'', hlev''⟩ hgk' hhk hpo Et gt hgt kt' ⟨sqt', hmult', hactt', hlevt'⟩
    kt'' ⟨sqt'', hmult'', hactt'', hlevt''⟩ hgkt' hgkt'' e₁ he₁ hk'e hk''e
  refine ⟨asIso e₁, he₁, hmul, ?_, hlev, hk'e, hk''e, ?_⟩
  · intro x
    apply hpo.hom_ext
    · rw [← Category.assoc, ← hact' x, Category.assoc, show (asIso e₁).hom = e₁ from rfl, hk'e, ← Category.assoc, hk'e, hactt' x]
    · rw [← Category.assoc, ← hact'' x, Category.assoc, show (asIso e₁).hom = e₁ from rfl, hk''e, ← Category.assoc, hk''e, hactt'' x]
  · show g ≫ e₁ = gt
    rw [← hgk', Category.assoc, hk'e, hgkt']

#print axioms solution

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd (solution)
