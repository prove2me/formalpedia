-- Prove2me | solution 1 for BlackScholesModel.callPrice_spot_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:44:50.954975+00:00
-- url     : https://prove2.me/submissions/59902c61-afe0-4d1c-9134-5d530dba5d63

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_dPlus_spot_tail_limits
import Theorems.Thm_BlackScholesModel_stdNormalCDF_tail_limits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The European call tends to zero as positive spot decreases to zero. -/
theorem solution (K r σ T t : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (ht : t < T) :
    Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0) := by
  let τ : ℝ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hdplus : Tendsto
      (fun S => dPlus S K r σ τ) (𝓝[>] 0) atBot :=
    (dPlus_spot_tail_limits K r σ τ hK hσ hτ).1
  have hdminus : Tendsto
      (fun S => dMinus S K r σ τ) (𝓝[>] 0) atBot := by
    have hh := Filter.tendsto_atBot_add_const_right
      (𝓝[>] (0 : ℝ)) (-(σ * Real.sqrt τ)) hdplus
    convert hh using 1 <;>
      first
      | rfl
      | (funext S; simp only [dMinus, sub_eq_add_neg])
  have hNplus : Tendsto
      (fun S => stdNormalCDF (dPlus S K r σ τ))
      (𝓝[>] 0) (𝓝 0) :=
    (stdNormalCDF_tail_limits.1).comp hdplus
  have hNminus : Tendsto
      (fun S => stdNormalCDF (dMinus S K r σ τ))
      (𝓝[>] 0) (𝓝 0) :=
    (stdNormalCDF_tail_limits.1).comp hdminus
  have hspot : Tendsto (fun S : ℝ => S) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hfirst : Tendsto
      (fun S => stdNormalCDF (dPlus S K r σ τ) * S)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hNplus.mul hspot
  have hsecond : Tendsto
      (fun S => stdNormalCDF (dMinus S K r σ τ) *
        K * Real.exp (-r * τ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using
      (hNminus.mul_const K).mul_const (Real.exp (-r * τ))
  have hprice := hfirst.sub hsecond
  convert hprice using 1 <;>
    first
    | rfl
    | (funext S; simp only [callPrice, τ])
    | ring
