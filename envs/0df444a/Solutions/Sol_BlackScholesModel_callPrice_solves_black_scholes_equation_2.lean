-- Prove2me | solution 2 for BlackScholesModel.callPrice_solves_black_scholes_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:32:16.480923+00:00
-- url     : https://prove2.me/submissions/3674c52d-56a6-4087-b4ae-66282b26dd8e

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

/-- Assemble the Black-Scholes equation, smoothness and boundary conditions. -/
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
      Tendsto (fun S => callPrice K r σ T S t -
          (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0)) ∧
    (∀ S : ℝ, 0 < S →
      Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T) (𝓝 (max (S - K) 0))) := by
  have hsmooth := callPrice_smooth_on_domain K r σ T hK hσ
  have hpde := callPrice_satisfies_pde K r σ T hK hσ
  obtain ⟨hzero, hinfty, hexpiry⟩ :=
    callPrice_boundary_limits K r σ T hK hσ
  exact ⟨hsmooth, hpde, hzero, hinfty, hexpiry⟩
