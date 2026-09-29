-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuli.exists_iso_comp_eq_of_isCoarseModuli
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b1e4fd8c-7ba8-5788-9360-9b9e6da5bc32

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_existsUnique_comp_eq_and_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open scoped Quaternion

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX')
    (hX' : IsCoarseModuli Λ N X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by
  obtain ⟨⟨g, ⟨hgπ, hgpt⟩, _⟩, hiso⟩ :=
    CerednikDrinfeld.QM.IsCoarseModuli.existsUnique_comp_eq_and_isIso hX hX'
  haveI : IsIso g := hiso g hgπ hgpt
  exact ⟨asIso g, hgπ, hgpt⟩

end S_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli (solution)
