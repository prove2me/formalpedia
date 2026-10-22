-- Prove2me | solution 1 for BirkhoffGlobalSection.validated_binding_global_sections_of_convexity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T14:42:57.044773+00:00
-- url     : https://prove2.me/submissions/109fab31-3fe4-493d-aedd-8908dc9cdc30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic
import Theorems.Thm_BirkhoffGlobalSection_positive_tangential_hessian
import Theorems.Thm_BirkhoffGlobalSection_numerical_range_subcritical
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_derivative_pos
import Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_on_strictly_convex_star_shaped_points
import Theorems.Thm_BirkhoffGlobalSection_validated_binding_orbits_transverse_hopf
import Theorems.Thm_BirkhoffGlobalSection_disk_like_global_section_of_transverse_hopf

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hconvex :
      Convex ℝ {y : Phase | ∃ s ∈ leftEnergyComponent μ c,
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}) :
    ∃ γr γd : PeriodicOrbit φ,
      IsAstronomicallyRetrogradeOrbit φ γr ∧
      IsAstronomicallyDirectOrbit φ γd ∧
      DiskLikeGlobalSurfaceOfSection φ γr ∧
      DiskLikeGlobalSurfaceOfSection φ γd := by
  have hμ1 : μ < 1 := by linarith
  have hc : belowFirstCriticalValue μ c := numerical_range_subcritical μ c hμ0 hμhalf hc0
  -- strict star-shapedness and the positive tangential Hessian (Proposition 4.4)
  have hstar := left_energy_component_radial_derivative_pos μ c hμ0 hμ1 hc
  have hhess := positive_tangential_hessian μ c hμ0.le hμhalf hc0 hc1
  -- every point of the component is strictly convex and star-shaped
  have hpt : ∀ s ∈ leftEnergyComponent μ c,
      IsStrictlyConvexStarShapedAt (leviCivitaHamiltonian μ c) s := by
    intro s hs
    refine ⟨⟨fun y hy => ?_, fun y hy v hv hdv => ?_⟩, hstar s hs⟩
    · rcases Set.mem_singleton_iff.1 hy with rfl
      exact hhess.1 y hs
    · rcases Set.mem_singleton_iff.1 hy with rfl
      exact hhess.2 y hs v hv hdv
  -- Hofer--Wysocki--Zehnder: strict convexity gives dynamical convexity
  have hdc : IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c) := by
    intro x T hx
    exact dynamically_convex_on_strictly_convex_star_shaped_points
      (leviCivitaHamiltonian μ c) x T
      ⟨hx.1, fun t => hpt _ (hx.2.1 t), hx.2.2.1, hx.2.2.2⟩
  -- the validated binding orbits and Hryniewicz's criterion
  obtain ⟨γr, γd, hr, hd, hhr, hhd⟩ :=
    validated_binding_orbits_transverse_hopf μ c hμ0 hμhalf hc0 hc1 φ hφ
  exact ⟨γr, γd, hr, hd,
    disk_like_global_section_of_transverse_hopf μ c hμ0 hμ1 hc hstar hdc φ hφ γr hhr,
    disk_like_global_section_of_transverse_hopf μ c hμ0 hμ1 hc hstar hdc φ hφ γd hhd⟩
