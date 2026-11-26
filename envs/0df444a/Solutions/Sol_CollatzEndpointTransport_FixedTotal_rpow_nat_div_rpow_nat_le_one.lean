-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.rpow_nat_div_rpow_nat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:20.268381+00:00
-- url     : https://prove2.me/submissions/5ef7e2d3-40d1-4c5c-b997-5f9ffca1fd22

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {a b : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (hb : 0 < b) (hab : a ≤ b) :
    ((a : ℝ) ^ theta) / ((b : ℝ) ^ theta) ≤ 1 := by
  rw [div_le_one (Real.rpow_pos_of_pos (by positivity) _)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) htheta
end CollatzEndpointTransport.FixedTotal
