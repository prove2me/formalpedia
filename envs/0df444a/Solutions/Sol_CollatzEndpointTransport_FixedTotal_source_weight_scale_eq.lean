-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.source_weight_scale_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:33.513359+00:00
-- url     : https://prove2.me/submissions/3c43ae04-f667-4fca-a59e-a7ad45791b46

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

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
    (htheta : theta < 1) :
    fixedSourceWeight N s *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) =
      (fixedSourceWeight N s) ^ (1 - theta) := by
  have hcardR : 0 < ((fixedSet N s).card : ℝ) := Nat.cast_pos.mpr hcard
  have hpow : 0 < (2 : ℝ) ^ N := by positivity
  have hweight : 0 < fixedSourceWeight N s :=
    div_pos hcardR hpow
  rw [Real.rpow_one_sub' hweight.le (by linarith)]
  unfold fixedSourceWeight
  rw [Real.div_rpow hcardR.le hpow.le]
  field_simp [hcardR.ne', hpow.ne',
    (Real.rpow_pos_of_pos hcardR _).ne',
    (Real.rpow_pos_of_pos hpow _).ne']
end CollatzEndpointTransport.FixedTotal
