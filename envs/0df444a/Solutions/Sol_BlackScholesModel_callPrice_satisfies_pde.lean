-- Prove2me | solution 1 for BlackScholesModel.callPrice_satisfies_pde
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:23:02.907892+00:00
-- url     : https://prove2.me/submissions/40d5ce0f-b9c1-4c95-abe5-b2bbe47b408d

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_call_delta
import Theorems.Thm_BlackScholesModel_call_theta
import Theorems.Thm_BlackScholesModel_gamma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ∀ S t : ℝ, 0 < S → t < T →
      deriv (fun t' => callPrice K r σ T S t') t
        + 1 / 2 * σ ^ 2 * S ^ 2
            * deriv (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S') S
        + r * S * deriv (fun S' => callPrice K r σ T S' t) S
        - r * callPrice K r σ T S t = 0 := by
  intro S t hS ht
  have htheta := call_theta K r σ T S t hK hσ hS ht
  have hgamma := (gamma K r σ T S t hK hσ hS ht).1
  have hdelta := call_delta K r σ T S t hK hσ hS ht
  rw [htheta.deriv, hgamma.deriv, hdelta.deriv]
  simp only [callPrice]
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hτ0 : Real.sqrt (T - t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr ht))
  field_simp [hS0, hσ0, hτ0]
  ring
