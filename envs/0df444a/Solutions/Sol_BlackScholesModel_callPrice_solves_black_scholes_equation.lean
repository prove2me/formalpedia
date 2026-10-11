-- Prove2me | solution 1 for BlackScholesModel.callPrice_solves_black_scholes_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T11:50:06.307292+00:00
-- url     : https://prove2.me/submissions/fb49594e-f559-4d43-a8c1-34331041732b

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_callPrice_smooth_on_domain
import Theorems.Thm_BlackScholesModel_callPrice_satisfies_pde
import Theorems.Thm_BlackScholesModel_callPrice_boundary_limits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal

open BlackScholesModel

theorem solution (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => callPrice K r σ T p.1 p.2)
        {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < T} ∧
    (∀ S t : ℝ, 0 < S → t < T →
      deriv (fun t' => callPrice K r σ T S t') t
        + 1 / 2 * σ ^ 2 * S ^ 2
            * deriv (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S') S
        + r * S * deriv (fun S' => callPrice K r σ T S' t) S
        - r * callPrice K r σ T S t = 0) ∧
    (∀ t : ℝ, t < T → Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ t : ℝ, t < T →
      Tendsto (fun S => callPrice K r σ T S t - (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0)) ∧
    (∀ S : ℝ, 0 < S →
      Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T) (𝓝 (max (S - K) 0))) := by
  -- The three source-faithful analytic children must first be published,
  -- proved, and imported using their authoritative module names.
  rcases callPrice_boundary_limits K r σ T hK hσ with
    ⟨h_zero, h_infinity, h_expiry⟩
  exact ⟨callPrice_smooth_on_domain K r σ T hK hσ,
    callPrice_satisfies_pde K r σ T hK hσ,
    h_zero, h_infinity, h_expiry⟩
