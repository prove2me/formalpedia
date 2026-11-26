-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.IsCDDense.D_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:39.867798+00:00
-- url     : https://prove2.me/submissions/fb7672ee-931b-4498-9b5e-4002ea3863f5

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
    D ≤ 1 := h.2.2.1
end IsCDDense
end CollatzEndpointTransport.QuantitativeDensity
