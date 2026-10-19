-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_point_jTemplate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/6024d067-cb55-4f7e-811f-1b86b862ab24

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPointRelated_symm
import Theorems.Thm_CompactnessConjecture_symplecticPointRelated_of_quadrangle_common_neighbor
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_base_center_related
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_bases_unrelated
import Theorems.Thm_CompactnessConjecture_symplecticPoint_point_class_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (p : Fin 4 → SymplecticPoint K)
    (c : Fin 2 → Fin 2 → SymplecticPoint K)
    (hbase : ∀ base : Fin 4,
      hom (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ (copy center : Fin 2),
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center)) : False := by
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) (base : Fin 3) :
      θ copy (.inl (.inl base)) =
        .inl (p (jBase copy base)) := by
    change hom (jThetaVertex copy (.inl (.inl base))) = _
    simpa [jThetaVertex] using hbase (jBase copy base)
  have hθcenter (copy center : Fin 2) :
      θ copy (.inl (.inr center)) =
        .inl (c copy center) := by
    change hom (jThetaVertex copy (.inl (.inr center))) = _
    simpa [jThetaVertex] using hcenter copy center
  have hcenters_inj (copy : Fin 2) :
      Function.Injective (c copy) := by
    intro i j hij
    have himage :
        θ copy (.inl (.inr i)) =
          θ copy (.inl (.inr j)) := by
      rw [hθcenter copy i, hθcenter copy j, hij]
    have hsource :
        (Sum.inl (Sum.inr i) : SubdivisionVertex 2) =
          .inl (.inr j) := (θ copy).injective himage
    exact Sum.inr.inj (Sum.inl.inj hsource)
  have hpoints_inj : Function.Injective p := by
    intro i j hij
    apply hbase_inj
    change hom (.inl (.inl i)) = hom (.inl (.inl j))
    rw [hbase i, hbase j, hij]
  have hyz : p 2 ≠ p 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hpoints_inj h)
  have hxx' : p 0 ≠ p 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hpoints_inj h)
  have hyz_unrelated :
      ¬ SymplecticPointRelated K (p 2) (p 3) := by
    have h := subdivisionPoint_bases_unrelated K (θ 0)
      (fun base => p (jBase 0 base)) (c 0)
      (hθbase 0) (hθcenter 0)
      (by decide : (1 : Fin 3) ≠ 2) 0
    simpa [jBase] using h
  have hrelated (copy : Fin 2) (base : Fin 3)
      (center : Fin 2) :
      SymplecticPointRelated K
        (c copy center) (p (jBase copy base)) :=
    symplecticPointRelated_symm K
      (subdivisionPoint_base_center_related K
        (θ copy) (hθbase copy base) (hθcenter copy center))
  have hcd : c 0 0 ≠ c 0 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 0 h)
  have hc'd' : c 1 0 ≠ c 1 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 1 h)
  have havoid := symplecticPoint_point_class_avoidance K
    (x := p 0) (x' := p 1) (y := p 2) (z := p 3)
    (c := c 0 0) (d := c 0 1)
    (c' := c 1 0) (d' := c 1 1)
    hyz hyz_unrelated hxx' hcd hc'd'
    (by simpa [jBase] using hrelated 0 0 0)
    (by simpa [jBase] using hrelated 0 1 0)
    (by simpa [jBase] using hrelated 0 2 0)
    (by simpa [jBase] using hrelated 0 0 1)
    (by simpa [jBase] using hrelated 0 1 1)
    (by simpa [jBase] using hrelated 0 2 1)
    (by simpa [jBase] using hrelated 1 0 0)
    (by simpa [jBase] using hrelated 1 1 0)
    (by simpa [jBase] using hrelated 1 2 0)
    (by simpa [jBase] using hrelated 1 0 1)
    (by simpa [jBase] using hrelated 1 1 1)
    (by simpa [jBase] using hrelated 1 2 1)
  have hjoin0 : jTemplate.Adj
      (.inl (.inl (0 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoin1 : jTemplate.Adj
      (.inl (.inl (1 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hleft := hom.map_rel hjoin0
  have hright := hom.map_rel hjoin1
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hleft
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hright
  rw [hbase 0] at hleft
  rw [hbase 1] at hright
  exact havoid
    (symplecticPointRelated_of_quadrangle_common_neighbor K
      hxx' hleft hright)
end CompactnessConjecture
