-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_point_jTemplate_of_first_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/17ae9ca4-b39e-4422-ac89-69a53fbec6cb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_base_of_point_base
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_point_jTemplate_of_bases

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
    (hfirst : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (0 : Fin 4))) = .inl p) : False := by
  obtain ⟨p₀, hp₀⟩ := hfirst
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hx : θ 0 (.inl (.inl (0 : Fin 3))) = .inl p₀ := by
    change hom (jThetaVertex 0 (.inl (.inl 0))) = _
    simpa [jThetaVertex, jBase] using hp₀
  have hy : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (2 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (1 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  have hz : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (3 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (2 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  obtain ⟨py, hpy⟩ := hy
  have hy' : θ 1 (.inl (.inl (1 : Fin 3))) = .inl py := by
    change hom (jThetaVertex 1 (.inl (.inl 1))) = _
    simpa [jThetaVertex, jBase] using hpy
  have hx' : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (1 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 1)
      (otherBase := (0 : Fin 3)) 0 hy'
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  apply symplecticQuadrangle_no_point_jTemplate_of_bases K
    hom hbase_inj hcopies
  intro base
  fin_cases base
  · exact ⟨p₀, hp₀⟩
  · exact hx'
  · exact ⟨py, hpy⟩
  · exact hz
end CompactnessConjecture
