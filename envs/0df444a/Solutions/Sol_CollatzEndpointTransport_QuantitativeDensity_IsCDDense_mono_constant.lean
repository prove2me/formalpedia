-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.mono_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:46.355105+00:00
-- url     : https://prove2.me/submissions/fdf0c65c-4714-4fba-a554-952f12360f3c

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_pos
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
    {S : Set ℕ} {C C' D : ℝ} (h : IsCDDense S C D) (hCC' : C ≤ C') :
    IsCDDense S C' D := by
  refine ⟨lt_of_lt_of_le h.C_pos hCC', h.D_pos, h.D_le_one, ?_⟩
  intro N hN
  calc
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
      h.bad_bound N hN
    _ ≤ C' * (N : ℝ) ^ (1 - D) :=
      mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (by positivity) _)
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
