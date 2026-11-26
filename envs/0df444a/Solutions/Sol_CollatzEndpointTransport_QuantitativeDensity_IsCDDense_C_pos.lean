-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.C_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:28.927266+00:00
-- url     : https://prove2.me/submissions/d1a5d511-8aff-4213-808f-6d3afce39922

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
namespace IsCDDense
theorem _root_.solution {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) :
    0 < C := h.1
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
