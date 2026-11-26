-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.degrade_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:39.904902+00:00
-- url     : https://prove2.me/submissions/6addd83f-403e-47a6-8f2f-bcbd985034bb

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_le_one
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_bad_bound

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
namespace IsCDDense
theorem _root_.solution
    {S : Set ℕ} {C D D' : ℝ} (h : IsCDDense S C D)
    (hD' : 0 < D') (hD'D : D' ≤ D) :
    IsCDDense S C D' := by
  refine ⟨h.C_pos, hD', le_trans hD'D h.D_le_one, ?_⟩
  intro N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow :
      (N : ℝ) ^ (1 - D) ≤ (N : ℝ) ^ (1 - D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
      h.bad_bound N hN
    _ ≤ C * (N : ℝ) ^ (1 - D') :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt h.C_pos)
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
