-- Prove2me | solution 1 for BirkhoffGlobalSection.quotient_retrograde_page_low_energy_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-02T20:21:29.294985+00:00
-- url     : https://prove2.me/submissions/71ffd3ef-c62c-48b2-a332-481bde902613
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_low_energy_tail
import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_convex_regularization
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends
import Mathlib.Topology.Order.Compact

open BirkhoffGlobalSection

set_option autoImplicit false

/-- A continuous positive regularized clock has uniform positive lower and
finite upper bounds on the compact energy component. -/
private theorem clock_bounds {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hcompact : IsCompact (leftEnergyComponent μ c))
    (hne : (leftEnergyComponent μ c).Nonempty) :
    ∃ a b : ℝ, 0 < a ∧ ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b := by
  have hcontinuous : ContinuousOn M.timeScale (leftEnergyComponent μ c) :=
    M.timeScale_continuous.mono M.contains_component
  obtain ⟨smin, hsmin, hmin⟩ := hcompact.exists_isMinOn hne hcontinuous
  obtain ⟨smax, hsmax, hmax⟩ := hcompact.exists_isMaxOn hne hcontinuous
  refine ⟨M.timeScale smin, M.timeScale smax, M.timeScale_pos smin hsmin, ?_⟩
  intro s hs
  exact ⟨hmin hs, hmax hs⟩

theorem solution :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by
  obtain ⟨ε, C, hε, hmodels⟩ := convex_regularization_model_low_energy_tail
  refine ⟨ε, C, hε, ?_⟩
  intro μ c hμ0 hμ1 hμε hC hc φ hφ hanti δ hδ
  obtain ⟨M⟩ := hmodels μ c hμ0 hμ1 hμε hC hc
  have hgeometry := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hcompact := hgeometry.1
  have hinv := hgeometry.2.2.1
  have hfree := hgeometry.2.2.2.1
  obtain ⟨a, b, ha, hclock⟩ :=
    clock_bounds M hcompact ⟨δ.point, δ.point.property⟩
  obtain ⟨P⟩ := geometric_retrograde_page_of_convex_regularization
    μ c hμ0 hμ1 hc M a b ha hclock φ hφ hanti δ hδ
  exact lifted_rational_page_descends φ hanti hinv hfree
    (antipodalTrajectoryDoubleLift φ hanti δ)
    (antipodal_trajectory_double_lift_is_double_cover φ hanti hfree δ) P
