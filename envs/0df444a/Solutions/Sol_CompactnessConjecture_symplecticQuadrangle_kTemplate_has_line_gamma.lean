-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_kTemplate_has_line_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/ac3d72a4-ef23-4499-af3b-c9adc71ebe48

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_point

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (hom : kTemplate →g symplecticQuadrangle K)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) :
    ∃ (i : Fin 2) (L : SymplecticLine K),
      (kGammaHomCopy hom hcopies i) kSpecifiedCenter = .inr L := by
  have hjoin : kTemplate.Adj
      ((0 : Fin 2), kSpecifiedCenter)
      ((1 : Fin 2), kSpecifiedCenter) := by
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kSpecifiedCenter]
  have hadj := hom.map_rel hjoin
  change (symplecticQuadrangle K).Adj
    (hom ((0 : Fin 2), kSpecifiedCenter))
    (hom ((1 : Fin 2), kSpecifiedCenter)) at hadj
  cases hzero : hom ((0 : Fin 2), kSpecifiedCenter) with
  | inl p =>
      rw [hzero] at hadj
      obtain ⟨L, hL, _⟩ :=
        symplecticQuadrangle_adjacent_to_point K hadj
      refine ⟨1, L, ?_⟩
      change hom (kGammaVertex 1 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hL
  | inr L =>
      refine ⟨0, L, ?_⟩
      change hom (kGammaVertex 0 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hzero
end CompactnessConjecture
