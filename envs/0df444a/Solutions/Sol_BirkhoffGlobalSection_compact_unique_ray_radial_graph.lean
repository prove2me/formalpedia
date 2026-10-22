-- Prove2me | solution 1 for BirkhoffGlobalSection.compact_unique_ray_radial_graph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:32:52.132243+00:00
-- url     : https://prove2.me/submissions/5199c66f-3197-4d98-941d-c8000a10732d

import Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_radius_continuous
import Theorems.Thm_BirkhoffGlobalSection_unique_ray_radial_cover

open BirkhoffGlobalSection

theorem solution (S : Set Phase)
    (hcompact : IsCompact S)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈ S) :
    ∃ ρ : {x : Phase // x ∈ unitThreeSphere} → ℝ,
      Continuous ρ ∧
      (∀ x, 0 < ρ x) ∧
      S = Set.range (fun x : {x : Phase // x ∈ unitThreeSphere} =>
        (fun i : Fin 4 => ρ x * (x : Phase) i)) := by
  let ρ : {x : Phase // x ∈ unitThreeSphere} → ℝ :=
    fun x => Classical.choose (hunique x).exists
  refine ⟨ρ, ?_, ?_, ?_⟩
  · exact compact_unique_ray_radius_continuous S hcompact hzero hunique
  · intro x
    exact (Classical.choose_spec (hunique x).exists).1
  · exact unique_ray_radial_cover S hzero hunique
