-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.bad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:29.482904+00:00
-- url     : https://prove2.me/submissions/660893c8-011f-47f1-8334-842acb8ce94b

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
namespace IsCDDense
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (N : ℕ) (hN : 0 < N) :
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
  h.2.2.2 N hN
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
