-- Prove2me | solution 1 for BlackScholesModel.callPrice_large_spot_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:07:10.010639+00:00
-- url     : https://prove2.me/submissions/7ecc1d46-7889-4b0f-a3fc-87db634c4347

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_dPlus_spot_tail_limits
import Theorems.Thm_BlackScholesModel_stdNormalCDF_tail_limits
import Theorems.Thm_BlackScholesModel_call_upper_tail_spot_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The large-spot call residual vanishes after controlling the weighted tail. -/
theorem solution (K r σ T t : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (ht : t < T) :
    Tendsto (fun S => callPrice K r σ T S t -
        (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0) := by
  let τ : ℝ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hdplus : Tendsto (fun S => dPlus S K r σ τ) atTop atTop :=
    (dPlus_spot_tail_limits K r σ τ hK hσ hτ).2
  have hdminus : Tendsto (fun S => dMinus S K r σ τ) atTop atTop := by
    have hh := hdplus.atTop_add
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => -(σ * Real.sqrt τ)) atTop
        (𝓝 (-(σ * Real.sqrt τ))))
    convert hh using 1 <;>
      first
      | rfl
      | (funext S; simp only [dMinus, sub_eq_add_neg])
  have hNminus : Tendsto
      (fun S => stdNormalCDF (dMinus S K r σ τ)) atTop (𝓝 1) :=
    stdNormalCDF_tail_limits.2.comp hdminus
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have htail : Tendsto
      (fun S => 1 - stdNormalCDF (dMinus S K r σ τ))
      atTop (𝓝 0) := by
    simpa only [sub_self] using hone.sub hNminus
  have hdiscountTail : Tendsto
      (fun S => K * Real.exp (-r * τ) *
        (1 - stdNormalCDF (dMinus S K r σ τ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul htail
  have hweighted : Tendsto
      (fun S => S * (1 - stdNormalCDF (dPlus S K r σ τ)))
      atTop (𝓝 0) :=
    call_upper_tail_spot_product K r σ τ hK hσ hτ
  have hprice := hweighted.neg.add hdiscountTail
  convert hprice using 1 <;>
    first
    | rfl
    | (funext S; dsimp [callPrice, τ]; ring)
    | ring