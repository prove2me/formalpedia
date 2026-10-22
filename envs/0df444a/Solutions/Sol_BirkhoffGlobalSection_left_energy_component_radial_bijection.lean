-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_radial_bijection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:13:30.98261+00:00
-- url     : https://prove2.me/submissions/c5164adf-9b2e-43f8-b630-f60c5d2f8f20

import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_projection_continuous
import Theorems.Thm_BirkhoffGlobalSection_left_component_unique_ray_intersection

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere},
      Continuous f ∧ Function.Bijective f ∧
        ∀ s, (f s : Phase) =
          fun i => (s : Phase) i /
            Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) := by
  obtain ⟨f, hcont, hrad⟩ :=
    left_component_radial_projection_continuous μ c hμ0 hμ1 hc
  exact ⟨f, hcont,
    left_component_unique_ray_intersection μ c hμ0 hμ1 hc f hrad,
    hrad⟩
