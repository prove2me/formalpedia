-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_point_jTemplate_of_bases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/0d363353-12e2-467c-96ec-389787976b8d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_center_of_point_base
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_point_jTemplate

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
    (hpoint : ∀ base : Fin 4,
      ∃ p : SymplecticPoint K,
        hom (.inl (.inl base)) = .inl p) : False := by
  classical
  let p : Fin 4 → SymplecticPoint K :=
    fun base => Classical.choose (hpoint base)
  have hp (base : Fin 4) :
      hom (.inl (.inl base)) = .inl (p base) :=
    Classical.choose_spec (hpoint base)
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) :
      θ copy (.inl (.inl (0 : Fin 3))) =
        .inl (p (jBase copy 0)) := by
    change hom (jThetaVertex copy (.inl (.inl 0))) = _
    simpa [jThetaVertex] using hp (jBase copy 0)
  have hcenter_exists (copy center : Fin 2) :
      ∃ q : SymplecticPoint K,
        hom (.inl (.inr (copy, center))) = .inl q := by
    have h := subdivisionPoint_center_of_point_base K
      (θ copy) (center := center) (hθbase copy)
    change ∃ q : SymplecticPoint K,
      hom (jThetaVertex copy (.inl (.inr center))) = .inl q at h
    simpa [jThetaVertex] using h
  let c : Fin 2 → Fin 2 → SymplecticPoint K :=
    fun copy center => Classical.choose (hcenter_exists copy center)
  have hc (copy center : Fin 2) :
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center) :=
    Classical.choose_spec (hcenter_exists copy center)
  exact symplecticQuadrangle_no_point_jTemplate K hom
    hbase_inj hcopies p c hp hc
end CompactnessConjecture
