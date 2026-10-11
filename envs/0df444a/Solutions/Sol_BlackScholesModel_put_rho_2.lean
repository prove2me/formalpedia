-- Prove2me | solution 2 for BlackScholesModel.put_rho
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:22:17.161432+00:00
-- url     : https://prove2.me/submissions/7cd2a7fc-addf-4503-a2af-b0608ef9a00c

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_call_rho
import Theorems.Thm_BlackScholesModel_put_call_parity
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Differentiate put-call parity in the interest rate to obtain put rho. -/
theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun r' => putPrice K r' σ T S t)
      (-(K * (T - t) * Real.exp (-r * (T - t)) *
        stdNormalCDF (-dMinus S K r σ (T - t)))) r := by
  let τ : ℝ := T - t
  have hC := call_rho K r σ T S t hK hσ hS ht
  have harg : HasDerivAt (fun u : ℝ => -u * τ) (-τ) r := by
    convert (hasDerivAt_id r).neg.mul_const τ using 1 <;>
      first
      | rfl
      | (funext u; dsimp [id]; ring)
      | ring
  have hExp : HasDerivAt (fun u : ℝ => Real.exp (-u * τ))
      (Real.exp (-r * τ) * (-τ)) r :=
    (Real.hasDerivAt_exp _).comp r harg
  have hdisc : HasDerivAt
      (fun u : ℝ => (K * Real.exp (-u * τ) - S))
      (K * (Real.exp (-r * τ) * (-τ))) r := by
    simpa only [sub_eq_add_neg] using
      (hExp.const_mul K).add_const (-S)
  have hP : HasDerivAt
      (fun u : ℝ => (K * Real.exp (-u * τ) - S) +
        callPrice K u σ T S t)
      (K * (Real.exp (-r * τ) * (-τ)) +
        K * τ * Real.exp (-r * τ) *
          stdNormalCDF (dMinus S K r σ τ)) r := by
    convert hdisc.add hC using 1 <;>
      first
      | rfl
      | (funext u; dsimp [τ]; ring)
      | ring
  have hfun :
      (fun u : ℝ => putPrice K u σ T S t) =
      (fun u : ℝ => (K * Real.exp (-u * τ) - S) +
        callPrice K u σ T S t) := by
    funext u
    convert put_call_parity K u σ T S t using 1 <;> ring
  have heq :
      K * (Real.exp (-r * τ) * (-τ)) +
        K * τ * Real.exp (-r * τ) *
          stdNormalCDF (dMinus S K r σ τ) =
      -(K * τ * Real.exp (-r * τ) *
        stdNormalCDF (-dMinus S K r σ τ)) := by
    rw [stdNormalCDF_neg]
    ring
  rw [← hfun] at hP
  rw [heq] at hP
  simpa only [τ] using hP
