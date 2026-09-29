-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b1ed9e86-36f3-5988-a300-e5dd2dd941df

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian

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
    (hgh' : gB ≫ h' = g') (hgh'' : gB ≫ h'' = g'') :
    ∃ (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (g : E₀.A ⟶ E.A)
      (_ : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) E E₀ g)
      (k' : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
      (k'' : E''.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k''),
      g' ≫ k' = g ∧ g'' ≫ k'' = g ∧ h' ≫ k' = h'' ≫ k'' ∧

      ∀ (Et : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (gt : E₀.A ⟶ Et.A)
        (_ : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) Et E₀ gt)
        (kt' : E'.A ⟶ Et.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') Et E' kt')
        (kt'' : E''.A ⟶ Et.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') Et E'' kt''),
        g' ≫ kt' = gt → g'' ≫ kt'' = gt →
        ∃ (e : E.A ≅ Et.A) (he : e.hom ≫ Et.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
            mapPt e.hom he (E.L.mul t P Q) = Et.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ Et.act x) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
            FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt e.hom he P)) ∧
          g ≫ e.hom = gt := by
  obtain ⟨E, k', hk', k'', hk'', hhk, hpo⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent B B' B'' φ' φ'' hφ's hφ''s hφ'n hφ''n E' E'' EB h' hh' h'' hh''
  have hg : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) E E₀ (g' ≫ k') :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (pullbackFst φ' φ'') ρ' E E' E₀ k' g' hk' hg'
  have hgk'' : g'' ≫ k'' = g' ≫ k' := by
    rw [← hgh'', ← hgh', Category.assoc, Category.assoc, hhk]
  refine ⟨E, g' ≫ k', hg, k', hk', k'', hk'', rfl, hgk'', hhk, ?_⟩
  intro Et gt hgt kt' hkt' kt'' hkt'' h1 h2
  obtain ⟨e, he, hmul, hact, hlev, -, -, hge⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd O E₀ B B' B'' ψ ψ' ψ'' ρ ρ' ρ'' hρ hρ' hρ'' hρker hρ'ker hρ''ker hρψ hρ'ψ hρ''ψ φ' φ'' hφ' hφ'' hφ'ρ hφ''ρ
      hφ's hφ''s hφ'n hφ''n E' g' hg' E'' g'' hg'' EB gB hgB h' hh' h'' hh'' hgh' hgh''
      E (g' ≫ k') hg k' hk' k'' hk'' rfl hhk hpo Et gt hgt kt' hkt' kt'' hkt'' h1 h2
  exact ⟨e, he, hmul, hact, hlev, hge⟩

#print axioms solution

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing (solution)
