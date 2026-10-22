-- Prove2me | solution 2 for BirkhoffGlobalSection.near_equal_mass_quotient_retrograde_page
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T14:44:28.585985+00:00
-- url     : https://prove2.me/submissions/2fd15b56-1556-45e5-b2a6-979f1fba03be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_near_critical
import Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_away_from_critical
import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_convex_regularization
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
import Theorems.Thm_BirkhoffGlobalSection_lifted_rational_page_descends
import Mathlib.Topology.Order.Compact

open BirkhoffGlobalSection

set_option autoImplicit false

/-- A continuous positive regularized clock is bounded above and away from zero
on the compact energy component. -/
private theorem clock_bounds_of_compact {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hcompact : IsCompact (leftEnergyComponent μ c))
    (hne : (leftEnergyComponent μ c).Nonempty) :
    ∃ a b : ℝ, 0 < a ∧ ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b := by
  have hcontinuous : ContinuousOn M.timeScale (leftEnergyComponent μ c) :=
    M.timeScale_continuous.mono M.contains_component
  obtain ⟨smin, hsmin, hmin⟩ := hcompact.exists_isMinOn hne hcontinuous
  obtain ⟨smax, hsmax, hmax⟩ := hcompact.exists_isMaxOn hne hcontinuous
  exact ⟨M.timeScale smin, M.timeScale smax, M.timeScale_pos smin hsmin,
    fun s hs => ⟨hmin hs, hmax hs⟩⟩

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε₀ → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by
  obtain ⟨εcrit, η, hεcrit, hη, hcrit⟩ := quotient_retrograde_page_near_critical
  obtain ⟨εaway, hεaway, haway⟩ := convex_regularization_model_away_from_critical η hη
  refine ⟨min εcrit εaway, lt_min hεcrit hεaway, ?_⟩
  intro μ c hμ0 hμ1 hμ hsub φ hφ hanti δ hδ
  by_cases hnear : c < 2 + η
  · exact hcrit μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_left _ _)) hnear hsub φ hφ hanti δ hδ
  · obtain ⟨M⟩ := haway μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_right _ _))
      (not_lt.mp hnear) hsub
    have hgeometry := left_energy_component_geometry μ c hμ0 hμ1 hsub
    obtain ⟨a, b, ha, hclock⟩ :=
      clock_bounds_of_compact M hgeometry.1 ⟨δ.point, δ.point.property⟩
    obtain ⟨P⟩ := geometric_retrograde_page_of_convex_regularization
      μ c hμ0 hμ1 hsub M a b ha hclock φ hφ hanti δ hδ
    exact lifted_rational_page_descends φ hanti hgeometry.2.2.1 hgeometry.2.2.2.1
      (antipodalTrajectoryDoubleLift φ hanti δ)
      (antipodal_trajectory_double_lift_is_double_cover φ hanti hgeometry.2.2.2.1 δ) P
