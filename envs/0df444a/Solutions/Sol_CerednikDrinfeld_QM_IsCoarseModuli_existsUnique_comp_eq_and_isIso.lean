-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuli.existsUnique_comp_eq_and_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d4a7ebd3-1efd-564e-b09b-f0f6799d6c78

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_existsUnique_comp_eq_and_isIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
    {X : Scheme.{0}} {πX : X ⟶ Spec (CommRingCat.of B)}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX}
    (hX : IsCoarseModuli Λ N X πX pt)
    {X' : Scheme.{0}} {πX' : X' ⟶ Spec (CommRingCat.of B)}
    {pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX'}
    (hX' : IsCoarseModuli Λ N X' πX' pt') :
    (∃! g : X ⟶ X', g ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ g) ∧
    ∀ g : X ⟶ X', g ≫ πX' = πX →
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ g) → IsIso g := by
  obtain ⟨g, ⟨hg1, hg2⟩, hguniq⟩ := hX.univ X' πX' pt' hX'.pt_iso hX'.pt_pullback
  obtain ⟨g', ⟨hg'1, hg'2⟩, -⟩ := hX'.univ X πX pt hX.pt_iso hX.pt_pullback
  have h1 : g ≫ g' = 𝟙 _ := by
    apply (hX.univ X πX pt hX.pt_iso hX.pt_pullback).unique
    · exact ⟨by rw [Category.assoc, hg'1, hg1], fun S _ s E => by rw [← Category.assoc, ← hg2 S s E, ← hg'2 S s E]⟩
    · exact ⟨by simp, fun S _ s E => by simp⟩
  have h2 : g' ≫ g = 𝟙 _ := by
    apply (hX'.univ X' πX' pt' hX'.pt_iso hX'.pt_pullback).unique
    · exact ⟨by rw [Category.assoc, hg1, hg'1], fun S _ s E => by rw [← Category.assoc, ← hg'2 S s E, ← hg2 S s E]⟩
    · exact ⟨by simp, fun S _ s E => by simp⟩
  refine ⟨⟨g, ⟨hg1, hg2⟩, fun y hy => hguniq y hy⟩, fun k hk1 hk2 => ?_⟩
  have hk : k = g := hguniq k ⟨hk1, hk2⟩
  subst hk
  exact ⟨⟨g', h1, h2⟩⟩

end S_CerednikDrinfeld_QM_IsCoarseModuli_existsUnique_comp_eq_and_isIso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_existsUnique_comp_eq_and_isIso (solution)
