-- Prove2me | solution 1 for BlackScholesModel.callPrice_boundary_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:40:16.100563+00:00
-- url     : https://prove2.me/submissions/dd7812d3-5bcd-406a-b536-5dcbf6652a07

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_callPrice_spot_zero_limit
import Theorems.Thm_BlackScholesModel_callPrice_large_spot_limit
import Theorems.Thm_BlackScholesModel_callPrice_expiry_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Collect the zero-spot, large-spot and expiry boundary limits. -/
theorem solution (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    (∀ t : ℝ, t < T → Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ t : ℝ, t < T →
      Tendsto (fun S => callPrice K r σ T S t -
        (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0)) ∧
    (∀ S : ℝ, 0 < S →
      Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T)
        (𝓝 (max (S - K) 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact callPrice_spot_zero_limit K r σ T t hK hσ ht
  · intro t ht
    exact callPrice_large_spot_limit K r σ T t hK hσ ht
  · intro S hS
    exact callPrice_expiry_limit K r σ T S hK hσ hS
