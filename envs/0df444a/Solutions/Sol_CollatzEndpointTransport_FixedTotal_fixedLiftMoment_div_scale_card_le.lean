-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedLiftMoment_div_scale_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:51.473908+00:00
-- url     : https://prove2.me/submissions/494b7208-a2a1-4b30-b633-c84e747bbd6f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_real_fixed_lift_le_scale_mul_majorant

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcard : 0 < (fixedSet N s).card) :
    fixedLiftMoment N s theta /
        ((((2 : ℝ) ^ N) ^ theta) * ((fixedSet N s).card : ℝ)) ≤
      fixedReverseMajorantAverage N s theta := by
  have hden :
      0 < (((2 : ℝ) ^ N) ^ theta) * ((fixedSet N s).card : ℝ) := by
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (by exact_mod_cast hcard)
  unfold fixedLiftMoment fixedReverseMajorantAverage
  apply (div_le_div_iff₀ hden (by exact_mod_cast hcard :
    (0 : ℝ) < (fixedSet N s).card)).2
  calc
    (∑ c ∈ fixedSet N s,
        (((3 ^ s + syracuseNumerator c : ℕ) : ℝ) ^ theta)) *
          ((fixedSet N s).card : ℝ) ≤
        (∑ c ∈ fixedSet N s,
          (((2 : ℝ) ^ N) ^ theta) * realReverseMajorant theta c) *
            ((fixedSet N s).card : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (sum_le_sum fun c hc =>
          real_fixed_lift_le_scale_mul_majorant htheta0 htheta1 c hc)
        (Nat.cast_nonneg _)
    _ = ((((2 : ℝ) ^ N) ^ theta) *
          ((fixedSet N s).card : ℝ)) *
        (∑ c ∈ fixedSet N s, realReverseMajorant theta c) := by
      rw [← Finset.mul_sum]
      ring
    _ = (∑ c ∈ fixedSet N s, realReverseMajorant theta c) *
        ((((2 : ℝ) ^ N) ^ theta) *
          ((fixedSet N s).card : ℝ)) := by ring
end CollatzEndpointTransport.FixedTotal
