-- Prove2me | solution 1 for BirkhoffGlobalSection.lifted_retrograde_page_near_critical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T00:47:49.623184+00:00
-- url     : https://prove2.me/submissions/b739b89b-d480-4c76-b609-d571f4c276c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_near_critical
import Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_dynamical_convexity

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by
  obtain ⟨ε, η, hε, hη, hconvex⟩ := dynamically_convex_near_critical
  refine ⟨ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμε hcη hc φ hφ hanti δ hδ
  exact geometric_retrograde_page_of_dynamical_convexity μ c hμ0 hμ1 hc
    (hconvex μ c hμ0 hμ1 hμε hcη hc) φ hφ hanti δ hδ
