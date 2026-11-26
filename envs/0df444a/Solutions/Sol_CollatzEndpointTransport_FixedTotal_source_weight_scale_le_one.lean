-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.source_weight_scale_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:22.59413+00:00
-- url     : https://prove2.me/submissions/1a31c867-2d3c-424f-90d9-62b305cfc52a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_le_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_eq

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta : ℝ}
    (hcard : 0 < (fixedSet N s).card)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    fixedSourceWeight N s *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) ≤ 1 := by
  rw [source_weight_scale_eq hcard htheta1]
  exact Real.rpow_le_one
    (fixedSourceWeight_nonneg N s)
    (fixedSourceWeight_le_one N s)
    (by linarith)
end CollatzEndpointTransport.FixedTotal
