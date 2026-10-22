-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_left_energy_component
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T18:37:34.584436+00:00
-- url     : https://prove2.me/submissions/70a471f2-006c-4ba8-a83f-0f385f057751

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_star_shaped_level_set_convex
import Theorems.Thm_BirkhoffGlobalSection_positive_tangential_hessian
import Theorems.Thm_BirkhoffGlobalSection_numerical_range_subcritical
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_compact
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_interior_negative
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    Convex ℝ {y : Phase | ∃ s ∈ leftEnergyComponent μ c, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} := by
  have hμ1 : μ < 1 := by linarith
  have hc := numerical_range_subcritical μ c hμ0 hμhalf hc0
  refine star_shaped_level_set_convex (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c)
    (left_energy_component_compact μ c hμ0 hμ1 hc)
    (fun s hs => (connectedComponentIn_subset _ _ hs).1)
    (left_energy_component_regular μ c hμ0 hμ1 hc)
    (positive_tangential_hessian μ c hμ0.le hμhalf hc0 hc1)
    (left_component_ray_exists μ c hμ0 hμ1 hc)
    (left_component_ray_unique_scale μ c hμ0 hμ1 hc) ?_
  intro x hx R hR hRx r hr0 hrR
  rcases hr0.lt_or_eq with hr | hr
  · exact left_component_radial_interior_negative μ c hμ0 hμ1 hc x hx R hR hRx r hr hrR
  · -- the origin: `K(0) = -(1 - μ)/2 < 0`
    subst hr
    simp [leviCivitaHamiltonian, wNormSq, zNormSq]
    linarith
